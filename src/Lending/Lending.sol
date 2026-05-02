// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Ownable} from "@openzeppelin/contracts/access/Ownable.sol";
import {Ownable2Step} from "@openzeppelin/contracts/access/Ownable2Step.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {IERC20Metadata} from "@openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol";
import {SafeERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import {Pausable} from "@openzeppelin/contracts/utils/Pausable.sol";
import {ReentrancyGuard} from "@openzeppelin/contracts/utils/ReentrancyGuard.sol";
import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";
import {SafeCast} from "@openzeppelin/contracts/utils/math/SafeCast.sol";

import {ILendingPool} from "../interfaces/ILendingPool.sol";
import {IPriceOracle} from "../interfaces/IPriceOracle.sol";
import {LendingMath} from "./LendingMath.sol";

/// @title Lending — multi-asset lending pool with scaled-balance accounting and liquidation
///
/// @notice Accounting model — read this before attempting to modify anything:
///
///   Scale conventions — four different precision units live here. Mixing them is a common bug class:
///     - RAY (1e27): `supplyIndex`, `borrowIndex`, interest rates (per-year and per-second).
///     - WAD (1e18): USD values (asset value, total debt, total collateral), health factor (1e18 = 1.0).
///     - BPS (10_000): config params — `collateralFactorBps`, `liquidationThresholdBps`, `liquidationBonusBps`,
///                     `reserveFactorBps`, `closeFactorBps`, `irParams.optimalUtilizationBps`.
///     - Oracle (1e8): Chainlink-style raw price. Normalized to WAD via the helpers in `LendingMath`.
///
///   Scaled-balance invariant:
///     `user_underlying_amount = user_scaled × index / RAY` (floor rounded).
///     Both `supplyIndex` and `borrowIndex` monotonically increase over time. Suppliers' claim grows via supplyIndex;
///     borrowers' debt grows via borrowIndex. The delta between them × reserveFactor accrues to `accruedReserves`.
///
///   Rounding directions (all favor the protocol):
///     - supply: scaled amount rounded DOWN (user receives fewer scaled units).
///     - withdraw: scaled amount burned rounded UP (user pays more scaled).
///     - borrow: scaled amount rounded UP (borrower owes at least the requested).
///     - repay: scaled amount credited rounded DOWN (user pays off slightly less per token).
///
///   Health factor: `HF = sum(collateralValueUSD × liquidationThreshold) / sum(debtValueUSD)` in WAD.
///     HF >= 1e18 is healthy. HF < 1e18 is liquidatable.
///     Withdraw with no debt skips oracle reads (no HF check needed).
///
///   Liquidation: anyone can repay up to `closeFactor × debt` of a borrower with HF < 1e18 and receive the borrower's
///     collateral at a `liquidationBonus` discount. Liquidator receives collateral AS AN INTERNAL SUPPLY POSITION (no
///     external transfer of collateral tokens). Debt asset ≠ collateral asset. Borrower ≠ liquidator.
///
///   Pause matrix: `supply`, `borrow`, `liquidate` blocked while paused. `withdraw`, `repay`, `accrueInterest` always
///     available. `setBorrowEnabled(false)` / `setCollateralEnabled(false)` disable NEW actions only — liquidation of
///     existing positions still proceeds regardless of the toggle.
contract Lending is ILendingPool, Ownable2Step, ReentrancyGuard, Pausable {
    using SafeCast for uint256;
    using SafeERC20 for IERC20;

    uint256 public constant WAD = 1e18;
    uint256 public constant RAY = 1e27;
    uint256 public constant BPS = 10_000;
    uint256 public constant SECONDS_PER_YEAR = 365 days;

    uint256 public constant MIN_HEALTH_FACTOR = 1e18;
    uint256 public constant MAX_CLOSE_FACTOR_BPS = 10_000;
    uint256 public constant MAX_LIQ_BONUS_BPS = 2_000;
    uint256 public constant MAX_COLLATERAL_FACTOR_BPS = 9_000;
    uint256 public constant MAX_RESERVE_FACTOR_BPS = 5_000;
    uint256 public constant MAX_ORACLE_STALENESS = 1 hours;
    uint8 public constant ORACLE_DECIMALS = 8;
    uint8 public constant MIN_RESERVE_DECIMALS = 6;
    uint8 public constant MAX_RESERVE_DECIMALS = 18;
    uint256 public constant DUST_LIQUIDATION_THRESHOLD_WAD = 1e14;

    mapping(address => Reserve) public reserves;
    address[] public reserveList;

    mapping(address => mapping(address => uint256)) public userScaledSupply;
    mapping(address => mapping(address => uint256)) public userScaledBorrow;

    mapping(address => address[]) public userCollateralAssets;
    mapping(address => address[]) public userBorrowAssets;
    mapping(address => mapping(address => bool)) internal _hasCollateral;
    mapping(address => mapping(address => bool)) internal _hasBorrow;

    IPriceOracle public oracle;
    uint256 public closeFactorBps;

    /// @notice Sets the initial oracle and close factor.
    /// @param oracle_ The oracle used for USD pricing.
    /// @param closeFactorBps_ The initial close factor in basis points.
    constructor(IPriceOracle oracle_, uint256 closeFactorBps_) Ownable(msg.sender) {
        _validateOracle(oracle_);
        if (closeFactorBps_ > MAX_CLOSE_FACTOR_BPS) {
            revert CloseFactorTooHigh(closeFactorBps_, MAX_CLOSE_FACTOR_BPS);
        }

        oracle = oracle_;
        closeFactorBps = closeFactorBps_;
    }

    /// @notice Supplies an asset to the pool for `onBehalfOf`.
    /// @param asset The reserve asset being supplied.
    /// @param amount The raw token amount to supply.
    /// @param onBehalfOf The account credited with the resulting scaled balance.
    function supply(address asset, uint256 amount, address onBehalfOf) external nonReentrant whenNotPaused {
        if (amount == 0) revert ZeroAmount();
        if (onBehalfOf == address(0)) revert ZeroAddress();

        _accrueInterest(asset);

        Reserve storage reserve = _getReserveStorage(asset);
        IERC20 token = IERC20(asset);
        uint256 balanceBefore = token.balanceOf(address(this));
        token.safeTransferFrom(msg.sender, address(this), amount);
        uint256 received = token.balanceOf(address(this)) - balanceBefore;
        if (received != amount) revert UnsupportedToken(asset);

        // rounding: supply mints scaled balance DOWN to favor the protocol.
        uint256 scaledAmount = Math.mulDiv(amount, RAY, reserve.supplyIndex);
        if (scaledAmount == 0) revert ZeroAmount();

        userScaledSupply[onBehalfOf][asset] += scaledAmount;
        reserve.totalScaledSupply = (uint256(reserve.totalScaledSupply) + scaledAmount).toUint128();

        if (reserve.useAsCollateral && !_hasCollateral[onBehalfOf][asset] && msg.sender == onBehalfOf) {
            _hasCollateral[onBehalfOf][asset] = true;
            userCollateralAssets[onBehalfOf].push(asset);
        }

        emit Supplied(onBehalfOf, asset, amount, scaledAmount);
    }

    /// @notice Withdraws supplied liquidity to `to`.
    /// @dev If the caller has debt, the post-withdraw health factor must remain `>= MIN_HEALTH_FACTOR`.
    /// @param asset The reserve asset being withdrawn.
    /// @param amount The raw token amount to withdraw, or `type(uint256).max` for the full balance.
    /// @param to The recipient of the withdrawn tokens.
    /// @return withdrawn The actual token amount withdrawn.
    function withdraw(address asset, uint256 amount, address to) external nonReentrant returns (uint256 withdrawn) {
        if (amount == 0) revert ZeroAmount();
        if (to == address(0)) revert ZeroAddress();

        _accrueInterest(asset);

        Reserve storage reserve = _getReserveStorage(asset);
        uint256 scaledBalance = userScaledSupply[msg.sender][asset];
        uint256 supplyBalance = LendingMath.scaledToUnderlying(scaledBalance, reserve.supplyIndex, Math.Rounding.Floor);
        if (supplyBalance == 0) revert InsufficientSupply(asset, amount, 0);

        withdrawn = amount == type(uint256).max ? supplyBalance : Math.min(amount, supplyBalance);

        // rounding: withdraw burns scaled balance UP to favor the protocol.
        uint256 scaledAmount = Math.mulDiv(withdrawn, RAY, reserve.supplyIndex, Math.Rounding.Ceil);
        if (scaledAmount > scaledBalance) scaledAmount = scaledBalance;

        userScaledSupply[msg.sender][asset] = scaledBalance - scaledAmount;
        reserve.totalScaledSupply = (uint256(reserve.totalScaledSupply) - scaledAmount).toUint128();

        if (userScaledSupply[msg.sender][asset] == 0 && _hasCollateral[msg.sender][asset]) {
            _removeCollateralAsset(msg.sender, asset);
        }

        if (_userHasDebt(to)) {
            (,,, uint256 healthFactor) = _getUserAccountData(to);
            if (healthFactor < MIN_HEALTH_FACTOR) revert HealthFactorBelowThreshold(healthFactor);
        }

        uint256 liquidity = _availableLiquidity(asset, reserve.accruedReserves);
        if (liquidity < withdrawn) revert InsufficientLiquidity(asset, withdrawn, liquidity);

        IERC20(asset).safeTransfer(to, withdrawn);

        emit Withdrawn(msg.sender, asset, withdrawn, scaledAmount);
    }

    /// @notice Borrows an asset against the caller's collateral.
    /// @dev The post-borrow health factor must remain `>= MIN_HEALTH_FACTOR`.
    /// @param asset The reserve asset to borrow.
    /// @param amount The raw token amount to borrow.
    /// @param to The recipient of the borrowed tokens.
    function borrow(address asset, uint256 amount, address to) external nonReentrant whenNotPaused {
        if (amount == 0) revert ZeroAmount();
        if (to == address(0)) revert ZeroAddress();

        _accrueInterest(asset);

        Reserve storage reserve = _getReserveStorage(asset);
        if (!reserve.borrowEnabled) revert BorrowDisabled(asset);
        if (userScaledSupply[msg.sender][asset] != 0) revert SameAssetCollateralDebtNotAllowed();

        // rounding: borrow mints scaled debt UP so the borrower owes at least the requested amount.
        uint256 scaledAmount = Math.mulDiv(amount, RAY, reserve.borrowIndex, Math.Rounding.Ceil);
        if (scaledAmount == 0) revert ZeroAmount();

        userScaledBorrow[msg.sender][asset] += scaledAmount;
        reserve.totalScaledBorrow = (uint256(reserve.totalScaledBorrow) + scaledAmount).toUint128();

        if (!_hasBorrow[msg.sender][asset]) {
            _hasBorrow[msg.sender][asset] = true;
            userBorrowAssets[msg.sender].push(asset);
        }

        (,,, uint256 healthFactor) = _getUserAccountData(msg.sender);
        if (healthFactor < MIN_HEALTH_FACTOR) revert HealthFactorBelowThreshold(healthFactor);
        _requireWithinBorrowCapacity(msg.sender);

        uint256 liquidity = _availableLiquidity(asset, reserve.accruedReserves);
        if (liquidity < amount) revert InsufficientLiquidity(asset, amount, liquidity);

        IERC20(asset).safeTransfer(to, amount);

        emit Borrowed(msg.sender, asset, amount, scaledAmount);
    }

    /// @notice Repays debt for `onBehalfOf`.
    /// @param asset The reserve asset being repaid.
    /// @param amount The raw token amount to repay, or `type(uint256).max` for the full debt.
    /// @param onBehalfOf The borrower whose debt is reduced.
    /// @return repaid The actual token amount repaid.
    function repay(address asset, uint256 amount, address onBehalfOf) external nonReentrant returns (uint256 repaid) {
        if (amount == 0) revert ZeroAmount();
        if (onBehalfOf == address(0)) revert ZeroAddress();

        _accrueInterest(asset);

        Reserve storage reserve = _getReserveStorage(asset);
        uint256 scaledDebt = userScaledBorrow[onBehalfOf][asset];
        if (scaledDebt == 0) revert NoDebt(onBehalfOf, asset);

        uint256 debt = LendingMath.scaledToUnderlying(scaledDebt, reserve.borrowIndex, Math.Rounding.Ceil);
        repaid = amount == type(uint256).max ? debt : Math.min(amount, debt);

        // rounding: repay burns scaled debt DOWN to favor the protocol.
        uint256 scaledAmount = Math.mulDiv(repaid, RAY, reserve.borrowIndex);
        if (scaledAmount == 0) revert ZeroAmount();
        if (scaledAmount > scaledDebt) scaledAmount = scaledDebt;

        IERC20 token = IERC20(asset);
        uint256 balanceBefore = token.balanceOf(address(this));
        token.safeTransferFrom(msg.sender, address(this), repaid);
        uint256 received = token.balanceOf(address(this)) - balanceBefore;
        if (received != repaid) revert UnsupportedToken(asset);

        userScaledBorrow[onBehalfOf][asset] = scaledDebt - scaledAmount;
        reserve.totalScaledBorrow = (uint256(reserve.totalScaledBorrow) - scaledAmount).toUint128();

        if (userScaledBorrow[onBehalfOf][asset] == 0) {
            _removeBorrowAsset(onBehalfOf, asset);
        }

        emit Repaid(onBehalfOf, asset, repaid, scaledAmount, msg.sender);
    }

    /// @notice Liquidates an unhealthy borrow position by repaying debt and seizing collateral.
    /// @dev Liquidation is allowed only when the borrower's health factor is strictly `< MIN_HEALTH_FACTOR`.
    /// @param borrower The unhealthy borrower.
    /// @param collateralAsset The collateral reserve to seize.
    /// @param debtAsset The debt reserve to repay.
    /// @param debtToCover The requested debt amount to cover, subject to the close factor.
    /// @return debtRepaid The actual debt amount repaid.
    /// @return collateralSeized The actual collateral amount seized as a supply position.
    function liquidate(address borrower, address collateralAsset, address debtAsset, uint256 debtToCover)
        external
        nonReentrant
        whenNotPaused
        returns (uint256 debtRepaid, uint256 collateralSeized)
    {
        if (debtToCover == 0) revert ZeroAmount();
        if (borrower == address(0)) revert ZeroAddress();
        if (borrower == msg.sender) revert SelfLiquidation();
        if (collateralAsset == debtAsset) revert DebtAssetIsCollateralAsset();
        _accrueInterest(collateralAsset);
        _accrueInterest(debtAsset);

        Reserve storage collateralReserve = _getReserveStorage(collateralAsset);
        Reserve storage debtReserve = _getReserveStorage(debtAsset);

        (,,, uint256 healthFactor) = _getUserAccountData(borrower);
        if (healthFactor >= MIN_HEALTH_FACTOR) revert HealthFactorNotBelowThreshold(healthFactor);

        uint256 debtValueWad;
        uint256 liquidatorBonus;
        (debtRepaid, debtValueWad) = _repayLiquidationDebt(borrower, debtAsset, debtToCover, debtReserve);
        (collateralSeized, liquidatorBonus) = _transferLiquidationCollateral(
            borrower, msg.sender, collateralAsset, collateralReserve, debtValueWad, debtRepaid
        );

        emit Liquidated(borrower, msg.sender, collateralAsset, debtAsset, debtRepaid, collateralSeized, liquidatorBonus);
    }

    /// @notice Publicly accrues interest for a reserve without modifying user balances otherwise.
    /// @param asset The reserve asset to accrue.
    function accrueInterest(address asset) external {
        _accrueInterest(asset);
    }

    /// @notice Returns aggregate collateral, debt, borrowing power, and health for a user.
    /// @param user The user account.
    /// @return totalCollateralValueWad The total eligible collateral value in WAD.
    /// @return totalDebtValueWad The total debt value in WAD.
    /// @return availableBorrowsWad The remaining borrowing capacity in WAD using collateral factors.
    /// @return healthFactor The health factor in WAD, or `type(uint256).max` when debt is zero.
    function getUserAccountData(address user)
        external
        view
        returns (
            uint256 totalCollateralValueWad,
            uint256 totalDebtValueWad,
            uint256 availableBorrowsWad,
            uint256 healthFactor
        )
    {
        return _getUserAccountData(user);
    }

    /// @notice Returns the current supplied and borrowed balances for a user in one reserve.
    /// @param user The user account.
    /// @param asset The reserve asset.
    /// @return supplyBalance The supplied balance in raw token units.
    /// @return borrowBalance The borrowed balance in raw token units.
    function getUserReserveData(address user, address asset)
        external
        view
        returns (uint256 supplyBalance, uint256 borrowBalance)
    {
        Reserve memory reserve = _getUpdatedReserve(asset);
        supplyBalance =
            LendingMath.scaledToUnderlying(userScaledSupply[user][asset], reserve.supplyIndex, Math.Rounding.Floor);
        borrowBalance =
            LendingMath.scaledToUnderlying(userScaledBorrow[user][asset], reserve.borrowIndex, Math.Rounding.Ceil);
    }

    /// @notice Returns reserve data with indices and reserves simulated up to the current timestamp.
    /// @param asset The reserve asset.
    /// @return reserve The reserve snapshot.
    function getReserveData(address asset) external view returns (Reserve memory reserve) {
        return _getUpdatedReserve(asset);
    }

    /// @notice Returns the list of listed reserve assets.
    /// @return assets The reserve list.
    function getReserveList() external view returns (address[] memory assets) {
        return reserveList;
    }

    /// @notice Returns the user's tracked collateral-asset list.
    /// @param user The user account.
    /// @return assets The user's collateral asset list.
    function getUserCollateralAssets(address user) external view returns (address[] memory assets) {
        return userCollateralAssets[user];
    }

    /// @notice Returns the user's tracked borrow-asset list.
    /// @param user The user account.
    /// @return assets The user's borrow asset list.
    function getUserBorrowAssets(address user) external view returns (address[] memory assets) {
        return userBorrowAssets[user];
    }

    /// @notice Returns the current reserve utilization in RAY.
    /// @param asset The reserve asset.
    /// @return utilizationRay The utilization ratio in RAY.
    function utilizationRateRay(address asset) external view returns (uint256 utilizationRay) {
        Reserve memory reserve = _getUpdatedReserve(asset);
        return LendingMath.utilizationRateRay(reserve);
    }

    /// @notice Returns the current borrow rate per second in RAY.
    /// @param asset The reserve asset.
    /// @return rateRayPerSecond The borrow rate per second in RAY.
    function currentBorrowRateRay(address asset) external view returns (uint256 rateRayPerSecond) {
        Reserve memory reserve = _getUpdatedReserve(asset);
        (uint256 borrowRatePerYear,) = LendingMath.ratesRay(reserve, LendingMath.utilizationRateRay(reserve));
        return borrowRatePerYear / SECONDS_PER_YEAR;
    }

    /// @notice Returns the current supply rate per second in RAY.
    /// @param asset The reserve asset.
    /// @return rateRayPerSecond The supply rate per second in RAY.
    function currentSupplyRateRay(address asset) external view returns (uint256 rateRayPerSecond) {
        Reserve memory reserve = _getUpdatedReserve(asset);
        (, uint256 supplyRatePerYear) = LendingMath.ratesRay(reserve, LendingMath.utilizationRateRay(reserve));
        return supplyRatePerYear / SECONDS_PER_YEAR;
    }

    /// @notice Lists a new reserve.
    /// @param asset The reserve asset to list.
    /// @param irParams The reserve's interest-rate parameters.
    /// @param collateralFactorBps_ The collateral factor in basis points.
    /// @param liquidationThresholdBps The liquidation threshold in basis points.
    /// @param liquidationBonusBps The liquidation bonus in basis points.
    /// @param reserveFactorBps The reserve factor in basis points.
    /// @param borrowEnabled Whether borrowing this asset is enabled.
    /// @param useAsCollateral Whether supplied balances of this asset count as collateral.
    function listReserve(
        address asset,
        InterestRateParams calldata irParams,
        uint16 collateralFactorBps_,
        uint16 liquidationThresholdBps,
        uint16 liquidationBonusBps,
        uint16 reserveFactorBps,
        bool borrowEnabled,
        bool useAsCollateral
    ) external onlyOwner {
        if (asset == address(0)) revert ZeroAddress();
        if (reserves[asset].listed) revert ReserveAlreadyListed(asset);

        _validateReserveParams(collateralFactorBps_, liquidationThresholdBps, liquidationBonusBps, reserveFactorBps);

        uint8 decimals_ = IERC20Metadata(asset).decimals();
        if (decimals_ < MIN_RESERVE_DECIMALS || decimals_ > MAX_RESERVE_DECIMALS) revert UnsupportedToken(asset);
        reserves[asset] = Reserve({
            listed: true,
            borrowEnabled: borrowEnabled,
            useAsCollateral: useAsCollateral,
            decimals: decimals_,
            collateralFactorBps: collateralFactorBps_,
            liquidationThresholdBps: liquidationThresholdBps,
            liquidationBonusBps: liquidationBonusBps,
            reserveFactorBps: reserveFactorBps,
            totalScaledSupply: 0,
            totalScaledBorrow: 0,
            supplyIndex: RAY,
            borrowIndex: RAY,
            lastUpdateTimestamp: block.timestamp.toUint64(),
            accruedReserves: 0,
            irParams: irParams
        });
        reserveList.push(asset);

        emit ReserveListed(
            asset, decimals_, collateralFactorBps_, liquidationThresholdBps, liquidationBonusBps, reserveFactorBps
        );
    }

    /// @notice Updates reserve collateral and reserve-factor parameters.
    /// @param asset The reserve asset to update.
    /// @param collateralFactorBps_ The new collateral factor in basis points.
    /// @param liquidationThresholdBps The new liquidation threshold in basis points.
    /// @param liquidationBonusBps The new liquidation bonus in basis points.
    /// @param reserveFactorBps The new reserve factor in basis points.
    function setReserveParams(
        address asset,
        uint16 collateralFactorBps_,
        uint16 liquidationThresholdBps,
        uint16 liquidationBonusBps,
        uint16 reserveFactorBps
    ) external onlyOwner {
        _accrueInterest(asset);

        Reserve storage reserve = _getReserveStorage(asset);
        _validateReserveParams(collateralFactorBps_, liquidationThresholdBps, liquidationBonusBps, reserveFactorBps);

        reserve.collateralFactorBps = collateralFactorBps_;
        reserve.liquidationThresholdBps = liquidationThresholdBps;
        reserve.liquidationBonusBps = liquidationBonusBps;
        reserve.reserveFactorBps = reserveFactorBps;

        emit ReserveParamsUpdated(
            asset, collateralFactorBps_, liquidationThresholdBps, liquidationBonusBps, reserveFactorBps
        );
    }

    /// @notice Updates reserve interest-rate parameters.
    /// @param asset The reserve asset to update.
    /// @param irParams The new interest-rate parameters.
    function setInterestRateParams(address asset, InterestRateParams calldata irParams) external onlyOwner {
        _accrueInterest(asset);

        Reserve storage reserve = _getReserveStorage(asset);
        reserve.irParams = irParams;

        emit InterestRateParamsUpdated(
            asset,
            irParams.baseRateRayPerYear,
            irParams.slope1RayPerYear,
            irParams.slope2RayPerYear,
            irParams.optimalUtilizationBps
        );
    }

    /// @notice Enables or disables borrowing for a reserve.
    /// @param asset The reserve asset to update.
    /// @param enabled Whether borrowing should be enabled.
    function setBorrowEnabled(address asset, bool enabled) external onlyOwner {
        _accrueInterest(asset);

        Reserve storage reserve = _getReserveStorage(asset);
        reserve.borrowEnabled = enabled;

        emit BorrowEnabled(asset, enabled);
    }

    /// @notice Enables or disables use of a reserve as collateral.
    /// @param asset The reserve asset to update.
    /// @param enabled Whether collateral usage should be enabled.
    function setCollateralEnabled(address asset, bool enabled) external onlyOwner {
        _accrueInterest(asset);

        Reserve storage reserve = _getReserveStorage(asset);
        reserve.useAsCollateral = enabled;

        emit CollateralEnabled(asset, enabled);
    }

    /// @notice Updates the oracle used for USD pricing.
    /// @param newOracle The new oracle contract.
    function setOracle(IPriceOracle newOracle) external onlyOwner {
        _validateOracle(newOracle);

        oracle = newOracle;
        emit OracleUpdated(address(newOracle));
    }

    /// @notice Updates the global close factor.
    /// @param bps The new close factor in basis points.
    function setCloseFactor(uint256 bps) external onlyOwner {
        if (bps > MAX_CLOSE_FACTOR_BPS) revert CloseFactorTooHigh(bps, MAX_CLOSE_FACTOR_BPS);

        closeFactorBps = bps;
        emit CloseFactorUpdated(bps);
    }

    /// @notice Withdraws protocol reserves of an asset.
    /// @param asset The reserve asset whose reserves are being withdrawn.
    /// @param amount The raw token amount to withdraw from accrued reserves.
    /// @param to The recipient of the withdrawn reserves.
    function withdrawReserves(address asset, uint256 amount, address to) external onlyOwner nonReentrant {
        if (amount == 0) revert ZeroAmount();
        if (to == address(0)) revert ZeroAddress();

        _accrueInterest(asset);

        Reserve storage reserve = _getReserveStorage(asset);
        if (amount > reserve.accruedReserves) {
            revert InsufficientLiquidity(asset, amount, reserve.accruedReserves);
        }

        reserve.accruedReserves -= amount;
        IERC20(asset).safeTransfer(to, amount);

        emit ReservesWithdrawn(asset, amount, to);
    }

    /// @notice Pauses supply, borrow, and liquidation actions.
    function pause() external onlyOwner {
        _pause();
    }

    /// @notice Unpauses supply, borrow, and liquidation actions.
    function unpause() external onlyOwner {
        _unpause();
    }

    function _accrueInterest(address asset) internal {
        Reserve memory current = _getStoredReserve(asset);
        (Reserve memory updated, uint256 reserveDelta, bool changed) =
            LendingMath.updatedReserve(current, block.timestamp);
        if (!changed) return;

        reserves[asset] = updated;

        if (
            updated.supplyIndex != current.supplyIndex || updated.borrowIndex != current.borrowIndex
                || reserveDelta != 0
        ) {
            emit IndexUpdated(asset, updated.supplyIndex, updated.borrowIndex, reserveDelta);
        }
    }

    function _getUserAccountData(address user)
        internal
        view
        returns (
            uint256 totalCollateralValueWad,
            uint256 totalDebtValueWad,
            uint256 availableBorrowsWad,
            uint256 healthFactor
        )
    {
        uint256 collateralCapacityWad;
        uint256 liquidationCapacityWad;

        address[] storage collateralAssets = userCollateralAssets[user];
        for (uint256 i; i < collateralAssets.length; ++i) {
            address asset = collateralAssets[i];
            uint256 scaledBalance = userScaledSupply[user][asset];
            if (scaledBalance == 0) continue;

            Reserve memory reserve = _getUpdatedReserve(asset);

            uint256 supplyBalance =
                LendingMath.scaledToUnderlying(scaledBalance, reserve.supplyIndex, Math.Rounding.Floor);
            if (supplyBalance == 0) continue;

            uint256 valueWad = _getAssetValueWad(asset, supplyBalance);
            totalCollateralValueWad += valueWad;
            collateralCapacityWad += Math.mulDiv(valueWad, reserve.collateralFactorBps, BPS);
            liquidationCapacityWad += Math.mulDiv(valueWad, reserve.liquidationThresholdBps, BPS);
        }

        address[] storage borrowAssets = userBorrowAssets[user];
        for (uint256 i; i < borrowAssets.length; ++i) {
            address asset = borrowAssets[i];
            uint256 scaledDebt = userScaledBorrow[user][asset];
            if (scaledDebt == 0) continue;

            Reserve memory reserve = _getUpdatedReserve(asset);
            uint256 borrowBalance = LendingMath.scaledToUnderlying(scaledDebt, reserve.borrowIndex, Math.Rounding.Ceil);
            if (borrowBalance == 0) continue;

            totalDebtValueWad += _getAssetValueWad(asset, borrowBalance);
        }

        availableBorrowsWad = collateralCapacityWad > totalDebtValueWad ? collateralCapacityWad - totalDebtValueWad : 0;
        healthFactor =
            totalDebtValueWad == 0 ? type(uint256).max : Math.mulDiv(liquidationCapacityWad, WAD, totalDebtValueWad);
    }

    function _getUpdatedReserve(address asset) internal view returns (Reserve memory reserve) {
        reserve = _getStoredReserve(asset);
        (reserve,,) = LendingMath.updatedReserve(reserve, block.timestamp);
    }

    function _repayLiquidationDebt(
        address borrower,
        address debtAsset,
        uint256 debtToCover,
        Reserve storage debtReserve
    ) internal returns (uint256 debtRepaid, uint256 debtValueWad) {
        uint256 borrowerScaledDebt = userScaledBorrow[borrower][debtAsset];
        if (borrowerScaledDebt == 0) revert NoDebt(borrower, debtAsset);

        uint256 borrowerDebt =
            LendingMath.scaledToUnderlying(borrowerScaledDebt, debtReserve.borrowIndex, Math.Rounding.Ceil);
        uint256 maxCloseScaled = Math.mulDiv(borrowerScaledDebt, closeFactorBps, BPS, Math.Rounding.Ceil);
        uint256 maxCloseAmount =
            LendingMath.scaledToUnderlying(maxCloseScaled, debtReserve.borrowIndex, Math.Rounding.Ceil);
        if (debtToCover > maxCloseAmount) {
            revert LiquidationAmountExceedsCloseFactor(debtToCover, maxCloseAmount);
        }

        debtRepaid = Math.min(debtToCover, borrowerDebt);

        // rounding: liquidation burns scaled debt DOWN, same as repay, to favor the protocol.
        uint256 scaledDebtRepaid = Math.mulDiv(debtRepaid, RAY, debtReserve.borrowIndex);
        if (scaledDebtRepaid == 0) revert ZeroAmount();
        if (scaledDebtRepaid > borrowerScaledDebt) scaledDebtRepaid = borrowerScaledDebt;

        IERC20 debtToken = IERC20(debtAsset);
        uint256 debtBalanceBefore = debtToken.balanceOf(address(this));
        debtToken.safeTransferFrom(msg.sender, address(this), debtRepaid);
        uint256 received = debtToken.balanceOf(address(this)) - debtBalanceBefore;
        if (received != debtRepaid) revert UnsupportedToken(debtAsset);

        userScaledBorrow[borrower][debtAsset] = borrowerScaledDebt - scaledDebtRepaid;
        debtReserve.totalScaledBorrow = (uint256(debtReserve.totalScaledBorrow) - scaledDebtRepaid).toUint128();

        if (userScaledBorrow[borrower][debtAsset] == 0) {
            _removeBorrowAsset(borrower, debtAsset);
        }

        debtValueWad = _getAssetValueWad(debtAsset, debtRepaid);
    }

    function _transferLiquidationCollateral(
        address borrower,
        address liquidator,
        address collateralAsset,
        Reserve storage collateralReserve,
        uint256 debtValueWad,
        uint256 debtToCover
    ) internal returns (uint256 collateralSeized, uint256 liquidatorBonus) {
        uint256 baseCollateralAmount = _getAmountFromValueWad(collateralAsset, debtValueWad, Math.Rounding.Floor);
        uint256 maxBonusCollateral =
            Math.mulDiv(baseCollateralAmount, collateralReserve.liquidationBonusBps, BPS, Math.Rounding.Floor);
        uint256 maxCollateralSeize = baseCollateralAmount + maxBonusCollateral;

        uint256 seizeValueWad = Math.mulDiv(debtValueWad, BPS + collateralReserve.liquidationBonusBps, BPS);
        uint256 targetCollateralAmount = _getAmountFromValueWad(collateralAsset, seizeValueWad, Math.Rounding.Floor);
        if (targetCollateralAmount > maxCollateralSeize) {
            targetCollateralAmount = maxCollateralSeize;
        }

        uint256 borrowerScaledCollateral = userScaledSupply[borrower][collateralAsset];
        if (!_hasCollateral[borrower][collateralAsset]) {
            revert InsufficientSupply(collateralAsset, debtToCover, 0);
        }
        uint256 borrowerCollateral = LendingMath.scaledToUnderlying(
            borrowerScaledCollateral, collateralReserve.supplyIndex, Math.Rounding.Floor
        );
        bool dustLiquidation = _isDustLiquidation(collateralAsset, borrowerCollateral, debtValueWad);
        if (dustLiquidation && (targetCollateralAmount == 0 || targetCollateralAmount > borrowerCollateral)) {
            return _transferAllDustCollateral(
                borrower,
                liquidator,
                collateralAsset,
                borrowerScaledCollateral,
                borrowerCollateral,
                baseCollateralAmount
            );
        }
        if (targetCollateralAmount > borrowerCollateral) {
            revert InsufficientSupply(collateralAsset, targetCollateralAmount, borrowerCollateral);
        }

        // rounding: liquidation floors both value and scaled-balance conversions so fragmentation cannot over-seize.
        uint256 scaledCollateralTransfer =
            Math.mulDiv(targetCollateralAmount, RAY, collateralReserve.supplyIndex, Math.Rounding.Floor);
        if (scaledCollateralTransfer > borrowerScaledCollateral) {
            scaledCollateralTransfer = borrowerScaledCollateral;
        }
        if (scaledCollateralTransfer == 0 && dustLiquidation) {
            return _transferAllDustCollateral(
                borrower,
                liquidator,
                collateralAsset,
                borrowerScaledCollateral,
                borrowerCollateral,
                baseCollateralAmount
            );
        }

        collateralSeized = LendingMath.scaledToUnderlying(
            scaledCollateralTransfer, collateralReserve.supplyIndex, Math.Rounding.Floor
        );
        if (collateralSeized == 0) revert LiquidationSeizeTooSmall(debtToCover);

        liquidatorBonus = collateralSeized > baseCollateralAmount ? collateralSeized - baseCollateralAmount : 0;
        if (
            liquidatorBonus != 0 && liquidatorBonus * BPS > baseCollateralAmount * collateralReserve.liquidationBonusBps
        ) {
            maxCollateralSeize = baseCollateralAmount + maxBonusCollateral;
            if (maxCollateralSeize > borrowerCollateral) {
                maxCollateralSeize = borrowerCollateral;
            }
            scaledCollateralTransfer =
                Math.mulDiv(maxCollateralSeize, RAY, collateralReserve.supplyIndex, Math.Rounding.Floor);
            if (scaledCollateralTransfer > borrowerScaledCollateral) {
                scaledCollateralTransfer = borrowerScaledCollateral;
            }
            collateralSeized = LendingMath.scaledToUnderlying(
                scaledCollateralTransfer, collateralReserve.supplyIndex, Math.Rounding.Floor
            );
            if (collateralSeized == 0) revert LiquidationSeizeTooSmall(debtToCover);
            liquidatorBonus = collateralSeized > baseCollateralAmount ? collateralSeized - baseCollateralAmount : 0;
        }

        userScaledSupply[borrower][collateralAsset] = borrowerScaledCollateral - scaledCollateralTransfer;
        userScaledSupply[liquidator][collateralAsset] += scaledCollateralTransfer;

        if (userScaledSupply[borrower][collateralAsset] == 0 && _hasCollateral[borrower][collateralAsset]) {
            _removeCollateralAsset(borrower, collateralAsset);
        }
        if (scaledCollateralTransfer != 0 && !_hasCollateral[liquidator][collateralAsset]) {
            _hasCollateral[liquidator][collateralAsset] = true;
            userCollateralAssets[liquidator].push(collateralAsset);
        }
    }

    function _isDustLiquidation(address collateralAsset, uint256 borrowerCollateral, uint256 debtValueWad)
        internal
        view
        returns (bool)
    {
        if (borrowerCollateral == 0 || debtValueWad == 0 || debtValueWad > DUST_LIQUIDATION_THRESHOLD_WAD) {
            return false;
        }

        uint256 collateralValueWad = _getAssetValueWad(collateralAsset, borrowerCollateral);
        return collateralValueWad != 0 && collateralValueWad <= DUST_LIQUIDATION_THRESHOLD_WAD;
    }

    function _transferAllDustCollateral(
        address borrower,
        address liquidator,
        address collateralAsset,
        uint256 borrowerScaledCollateral,
        uint256 borrowerCollateral,
        uint256 baseCollateralAmount
    ) internal returns (uint256 collateralSeized, uint256 liquidatorBonus) {
        if (borrowerCollateral == 0) revert LiquidationSeizeTooSmall(0);

        userScaledSupply[borrower][collateralAsset] = 0;
        userScaledSupply[liquidator][collateralAsset] += borrowerScaledCollateral;

        if (_hasCollateral[borrower][collateralAsset]) {
            _removeCollateralAsset(borrower, collateralAsset);
        }
        if (borrowerScaledCollateral != 0 && !_hasCollateral[liquidator][collateralAsset]) {
            _hasCollateral[liquidator][collateralAsset] = true;
            userCollateralAssets[liquidator].push(collateralAsset);
        }

        collateralSeized = borrowerCollateral;
        liquidatorBonus = collateralSeized > baseCollateralAmount ? collateralSeized - baseCollateralAmount : 0;
    }

    function _getAssetValueWad(address asset, uint256 amount) internal view returns (uint256 valueWad) {
        if (amount == 0) return 0;

        Reserve memory reserve = _getStoredReserve(asset);
        (uint256 price, uint256 updatedAt) = oracle.getPrice(asset);
        if (price == 0) revert PriceZero(asset);
        if (block.timestamp - updatedAt > MAX_ORACLE_STALENESS) {
            revert PriceStale(asset, updatedAt, block.timestamp);
        }

        valueWad = LendingMath.assetValueWad(amount, reserve.decimals, price);
    }

    function _getAmountFromValueWad(address asset, uint256 valueWad) internal view returns (uint256 amount) {
        return _getAmountFromValueWad(asset, valueWad, Math.Rounding.Floor);
    }

    function _getAmountFromValueWad(address asset, uint256 valueWad, Math.Rounding rounding)
        internal
        view
        returns (uint256 amount)
    {
        if (valueWad == 0) return 0;

        Reserve memory reserve = _getStoredReserve(asset);
        (uint256 price, uint256 updatedAt) = oracle.getPrice(asset);
        if (price == 0) revert PriceZero(asset);
        if (block.timestamp - updatedAt > MAX_ORACLE_STALENESS) {
            revert PriceStale(asset, updatedAt, block.timestamp);
        }

        amount = LendingMath.amountFromValueWad(valueWad, reserve.decimals, price, rounding);
    }

    function _availableLiquidity(address asset, uint256 accruedReserves) internal view returns (uint256 liquidity) {
        accruedReserves;
        liquidity = IERC20(asset).balanceOf(address(this));
    }

    function _validateReserveParams(
        uint16 collateralFactorBps_,
        uint16 liquidationThresholdBps,
        uint16 liquidationBonusBps,
        uint16 reserveFactorBps
    ) internal pure {
        if (collateralFactorBps_ > MAX_COLLATERAL_FACTOR_BPS) {
            revert CollateralFactorTooHigh(collateralFactorBps_, MAX_COLLATERAL_FACTOR_BPS);
        }
        if (liquidationThresholdBps > MAX_COLLATERAL_FACTOR_BPS || liquidationThresholdBps < collateralFactorBps_) {
            revert LiquidationThresholdInvalid(collateralFactorBps_, liquidationThresholdBps);
        }
        if (liquidationBonusBps > MAX_LIQ_BONUS_BPS) {
            revert LiquidationBonusTooHigh(liquidationBonusBps, MAX_LIQ_BONUS_BPS);
        }
        if (uint256(liquidationThresholdBps) * (BPS + liquidationBonusBps) >= BPS * BPS) {
            revert LiquidationBonusTooHigh(liquidationBonusBps, MAX_LIQ_BONUS_BPS);
        }
        if (reserveFactorBps > MAX_RESERVE_FACTOR_BPS) {
            revert ReserveFactorTooHigh(reserveFactorBps, MAX_RESERVE_FACTOR_BPS);
        }
    }

    function _requireWithinBorrowCapacity(address user) internal view {
        (, uint256 totalDebtValueWad,,) = _getUserAccountData(user);
        if (totalDebtValueWad != 0) {
            uint256 collateralCapacityWad;
            address[] storage collateralAssets = userCollateralAssets[user];
            for (uint256 i; i < collateralAssets.length; ++i) {
                address asset = collateralAssets[i];
                uint256 scaledBalance = userScaledSupply[user][asset];
                if (scaledBalance == 0) continue;

                Reserve memory reserve = _getUpdatedReserve(asset);
                if (!reserve.useAsCollateral) continue;

                uint256 supplyBalance =
                    LendingMath.scaledToUnderlying(scaledBalance, reserve.supplyIndex, Math.Rounding.Floor);
                if (supplyBalance == 0) continue;

                collateralCapacityWad += Math.mulDiv(
                    _getAssetValueWad(asset, supplyBalance), reserve.collateralFactorBps, BPS
                );
            }

            if (totalDebtValueWad > collateralCapacityWad) {
                revert HealthFactorBelowThreshold(Math.mulDiv(collateralCapacityWad, WAD, totalDebtValueWad));
            }
        }
    }

    function _validateOracle(IPriceOracle oracle_) internal view {
        if (address(oracle_) == address(0)) revert ZeroAddress();
        if (oracle_.decimals() != ORACLE_DECIMALS) revert UnsupportedToken(address(oracle_));
    }

    function _userHasDebt(address user) internal view returns (bool) {
        return userBorrowAssets[user].length != 0;
    }

    function _removeCollateralAsset(address user, address asset) internal {
        _hasCollateral[user][asset] = false;
        address[] storage assets = userCollateralAssets[user];
        uint256 length = assets.length;
        for (uint256 i; i < length; ++i) {
            if (assets[i] == asset) {
                assets[i] = assets[length - 1];
                assets.pop();
                return;
            }
        }
    }

    function _removeBorrowAsset(address user, address asset) internal {
        _hasBorrow[user][asset] = false;
        address[] storage assets = userBorrowAssets[user];
        uint256 length = assets.length;
        for (uint256 i; i < length; ++i) {
            if (assets[i] == asset) {
                assets[i] = assets[length - 1];
                assets.pop();
                return;
            }
        }
    }

    function _getStoredReserve(address asset) internal view returns (Reserve memory reserve) {
        reserve = reserves[asset];
        if (!reserve.listed) revert ReserveNotListed(asset);
    }

    function _getReserveStorage(address asset) internal view returns (Reserve storage reserve) {
        reserve = reserves[asset];
        if (!reserve.listed) revert ReserveNotListed(asset);
    }
}

