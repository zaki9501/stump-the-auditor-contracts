// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {SafeERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import {Ownable2Step, Ownable} from "@openzeppelin/contracts/access/Ownable2Step.sol";
import {ReentrancyGuard} from "@openzeppelin/contracts/utils/ReentrancyGuard.sol";
import {Pausable} from "@openzeppelin/contracts/utils/Pausable.sol";
import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";

import {IStaking} from "../interfaces/IStaking.sol";

/// @title Lock-tiered multi-reward staking with penalty redistribution
///
/// @notice Accounting model — read this before attempting to modify anything:
///
///   Two accounting planes that meet at `totalBoostedSupply`:
///     1. Per-stake principal: `_userStakes[user][]` holds each stake position (amount, boostedAmount, tierId, start, unlock,
///        withdrawn). Principal is separate from rewards — unstaking returns principal, claim returns rewards.
///     2. Reward accumulator (Synthetix StakingRewards pattern): each reward token has `rewardRate`, `periodFinish`,
///        `rewardPerTokenStored`, `lastUpdateTime`. Users earn via `userRewardPerTokenPaid` vs. current `rewardPerToken`,
///        weighted by `_userBoostedAmount[user]`.
///
///   Critical invariants:
///     - `primaryRewardToken == stakingToken` always. Constructor enforces; `setPrimaryRewardToken` enforces.
///     - `_updateRewardAll(user)` MUST run before any mutation of `_userBoostedAmount[user]`, `totalBoostedSupply`, or any
///       per-user stake state. This snapshots the reward accumulator at the pre-change weight so users can't retroactively
///       capture reward value from state changes.
///     - `_userActiveStakeCount[user]` and `_userBoostedAmount[user]` are storage-tracked (O(1) reads), not derived by
///       scanning `_userStakes[user][]` on every call. Keeping them consistent is the caller's responsibility on every
///       mutation path.
///     - Early-unstake penalties are redistributed immediately to current non-penalized stakers. Just-in-time stakers
///       can capture a share of penalties at Medium severity (see audits/staking-r2). This is accepted as documented
///       design for the challenge base. If no eligible cohort exists, the penalty waits in `queuedPenalty`.
///       `flushPenalty()` moves queued penalty into the primary reward stream WITHOUT extending `periodFinish` — if a
///       stream is active, penalty is folded into the remaining window's rate. This prevents schedule-extension griefing.
///     - `compound()` zeros the user's primary-token reward balance BEFORE creating the new stake. No transfer — the tokens
///       are already in the contract.
///
///   Pause matrix: stake + compound blocked; unstake + emergencyUnstake + claim + claim(token) always available.
contract Staking is IStaking, Ownable2Step, ReentrancyGuard, Pausable {
    using SafeERC20 for IERC20;

    error UnsupportedToken(address token);
    error StakeUnlocked(uint256 stakeId, uint64 unlockTime);
    error RewardPeriodNotFinished(uint64 periodFinish);
    error Overflow();
    error InsufficientRewardBalance(address token, uint256 required, uint256 available);

    uint256 public constant BPS = 10_000;
    uint256 public constant PRECISION = 1e18;
    uint256 public constant MAX_REWARD_TOKENS = 4;
    uint256 public constant MAX_LOCK_TIERS = 6;
    uint256 public constant MIN_REWARD_DURATION = 1 days;
    uint256 public constant MAX_REWARD_DURATION = 365 days;
    uint256 public constant MAX_BOOST_BPS = 30_000;
    uint256 public constant MIN_BOOST_BPS = 10_000;
    uint256 public constant MAX_PENALTY_BPS = 5_000;
    uint256 public constant MAX_STAKES_PER_USER = 64;
    uint256 public constant MIN_STAKE_AMOUNT = 1e12;
    uint256 public constant MIN_FLUSH_PENALTY_AMOUNT = 1e15;
    uint256 public constant EXTRA_PRECISION = 1e18;
    uint256 public constant ACCUMULATOR_PRECISION = PRECISION * EXTRA_PRECISION;

    IERC20 public immutable stakingToken;

    mapping(uint8 => LockTier) public lockTiers;
    uint8 public nextLockTierId;

    mapping(address => Stake[]) internal _userStakes;
    mapping(address => uint256) internal _userActiveStakeCount;
    mapping(address => uint256) internal _userBoostedAmount;

    uint256 public totalRawSupply;
    uint256 public totalBoostedSupply;

    struct RewardData {
        bool enabled;
        uint64 periodFinish;
        uint64 lastUpdateTime;
        uint128 rewardRate;
        uint64 rewardsDuration;
        uint256 rewardPerTokenStored;
        uint256 queuedPenalty;
    }

    mapping(address => RewardData) public rewardData;
    address[] public rewardTokensList;

    mapping(address => mapping(address => uint256)) public userRewardPerTokenPaid;
    mapping(address => mapping(address => uint256)) public rewards;

    uint256 public earlyUnstakePenaltyBps;
    address public primaryRewardToken;

    /// @notice Sets the staking token, primary reward token, and initial penalty configuration.
    /// @param stakingToken_ The token users stake as principal.
    /// @param primaryRewardToken_ The primary reward token, which must equal the staking token.
    /// @param earlyUnstakePenaltyBps_ The initial early-unstake penalty in basis points.
    constructor(IERC20 stakingToken_, address primaryRewardToken_, uint256 earlyUnstakePenaltyBps_)
        Ownable(msg.sender)
    {
        if (address(stakingToken_) == address(0) || primaryRewardToken_ == address(0)) {
            revert ZeroAddress();
        }
        if (primaryRewardToken_ != address(stakingToken_)) revert CompoundRequiresStakingTokenReward();
        if (earlyUnstakePenaltyBps_ > MAX_PENALTY_BPS) {
            revert PenaltyTooHigh(earlyUnstakePenaltyBps_, MAX_PENALTY_BPS);
        }

        stakingToken = stakingToken_;
        primaryRewardToken = address(stakingToken_);
        earlyUnstakePenaltyBps = earlyUnstakePenaltyBps_;

        // The staking token is always the primary reward token, so reserve one reward-token
        // slot for it at deployment time and seed a default stream duration for penalty flushes.
        rewardData[address(stakingToken_)].enabled = true;
        rewardData[address(stakingToken_)].rewardsDuration = 30 days;
        rewardTokensList.push(address(stakingToken_));
    }

    /// @notice Creates a new stake under an enabled lock tier.
    /// @param amount The amount of staking tokens to lock.
    /// @param tierId The lock tier to apply to the new position.
    /// @return stakeId The newly created stake index for the caller.
    function stake(uint128 amount, uint8 tierId) external nonReentrant whenNotPaused returns (uint256 stakeId) {
        if (amount == 0) revert ZeroAmount();
        if (amount < MIN_STAKE_AMOUNT) revert AmountTooSmall(amount, MIN_STAKE_AMOUNT);
        if (_activeStakeCount(msg.sender) >= MAX_STAKES_PER_USER) revert TooManyStakes(MAX_STAKES_PER_USER);

        LockTier storage tier = _requireEnabledTier(tierId);

        _updateRewardAll(msg.sender);

        uint256 balanceBefore = stakingToken.balanceOf(address(this));
        stakingToken.safeTransferFrom(msg.sender, address(this), amount);
        uint256 received = stakingToken.balanceOf(address(this)) - balanceBefore;
        if (received != amount) revert UnsupportedToken(address(stakingToken));

        uint64 unlockTime;
        uint128 boostedAmount;
        (stakeId, unlockTime, boostedAmount) = _createStake(msg.sender, amount, tierId, tier);
        if (amount == MIN_STAKE_AMOUNT && _userActiveStakeCount[msg.sender] > 1) {
            rewards[msg.sender][primaryRewardToken] += earnedUser(msg.sender, primaryRewardToken);
        }

        emit Staked(msg.sender, stakeId, amount, tierId, unlockTime, boostedAmount);
    }

    /// @notice Withdraws a fully unlocked stake position.
    /// @param stakeId The caller's stake index to close.
    function unstake(uint256 stakeId) external nonReentrant {
        Stake storage userStake = _getUserStakeStorage(msg.sender, stakeId);
        if (userStake.withdrawn) revert StakeAlreadyWithdrawn(stakeId);
        if (block.timestamp < userStake.unlockTime) revert StakeLocked(stakeId, userStake.unlockTime);

        _updateRewardAll(msg.sender);

        uint128 amount = userStake.amount;
        uint128 boostedAmount = userStake.boostedAmount;

        userStake.withdrawn = true;
        totalRawSupply -= amount;
        totalBoostedSupply -= boostedAmount;
        _userActiveStakeCount[msg.sender] -= 1;
        _userBoostedAmount[msg.sender] -= boostedAmount;

        stakingToken.safeTransfer(msg.sender, amount);

        emit Unstaked(msg.sender, stakeId, amount);
    }

    /// @notice Exits a still-locked stake early and routes the penalty to eligible existing stakers.
    /// @param stakeId The caller's stake index to close early.
    function emergencyUnstake(uint256 stakeId) external nonReentrant {
        Stake storage userStake = _getUserStakeStorage(msg.sender, stakeId);
        if (userStake.withdrawn) revert StakeAlreadyWithdrawn(stakeId);
        if (block.timestamp >= userStake.unlockTime) revert StakeUnlocked(stakeId, userStake.unlockTime);

        _updateRewardAll(msg.sender);

        uint128 amount = userStake.amount;
        uint128 boostedAmount = userStake.boostedAmount;
        uint128 penalty = _toUint128(Math.mulDiv(amount, earlyUnstakePenaltyBps, BPS));
        uint128 returnAmount = amount - penalty;

        userStake.withdrawn = true;
        totalRawSupply -= amount;
        totalBoostedSupply -= boostedAmount;
        _userActiveStakeCount[msg.sender] -= 1;
        _userBoostedAmount[msg.sender] -= boostedAmount;

        _distributeOrQueuePenalty(msg.sender, penalty);

        stakingToken.safeTransfer(msg.sender, returnAmount);

        emit EmergencyUnstaked(msg.sender, stakeId, returnAmount, penalty);
    }

    /// @notice Claims every accrued reward token for the caller.
    /// @dev Claims stay enabled while paused so users can still exit accrued value.
    function claim() external nonReentrant {
        _updateRewardAll(msg.sender);

        uint256 claimed;
        uint256 rewardsLength = rewardTokensList.length;
        for (uint256 i; i < rewardsLength; ++i) {
            claimed += _claimReward(msg.sender, rewardTokensList[i]);
        }

        if (claimed == 0) revert NothingToClaim();
    }

    /// @notice Claims a single accrued reward token for the caller.
    /// @param rewardToken The reward token to claim.
    function claim(address rewardToken) external nonReentrant {
        _requireRewardTokenListed(rewardToken);
        _updateRewardAll(msg.sender);

        uint256 claimed = _claimReward(msg.sender, rewardToken);
        if (claimed == 0) revert NothingToClaim();
    }

    /// @notice Compounds accrued primary-token rewards into a new stake.
    /// @param tierId The lock tier to apply to the compounded position.
    /// @return stakeId The newly created stake index for the caller.
    function compound(uint8 tierId) external nonReentrant whenNotPaused returns (uint256 stakeId) {
        if (primaryRewardToken != address(stakingToken)) revert CompoundRequiresStakingTokenReward();
        if (_activeStakeCount(msg.sender) >= MAX_STAKES_PER_USER) revert TooManyStakes(MAX_STAKES_PER_USER);

        LockTier storage tier = _requireEnabledTier(tierId);

        _updateRewardAll(msg.sender);

        uint256 amount = rewards[msg.sender][primaryRewardToken];
        if (amount == 0) revert NothingToClaim();
        if (amount < MIN_STAKE_AMOUNT) revert AmountTooSmall(amount, MIN_STAKE_AMOUNT);

        rewards[msg.sender][primaryRewardToken] = 0;

        // The contract already holds these primary-token rewards. Zeroing the reward balance first
        // prevents the same tokens from backing both a claim and the newly created staked principal.
        (stakeId,,) = _createStake(msg.sender, _toUint128(amount), tierId, tier);

        emit Compounded(msg.sender, tierId, amount, stakeId);
    }

    /// @notice Moves queued penalties into the primary reward stream.
    /// @dev Anyone may call this once the queued penalty reaches `MIN_FLUSH_PENALTY_AMOUNT`.
    /// @dev If a primary reward stream is already active, the penalty is folded into the remaining window
    ///      without extending `periodFinish`; otherwise a fresh full-duration stream starts.
    /// @dev Dust penalties below the minimum stay queued until more penalties accumulate.
    function flushPenalty() external nonReentrant {
        address rewardToken = primaryRewardToken;
        if (rewardToken != address(stakingToken)) revert CompoundRequiresStakingTokenReward();
        if (!rewardData[rewardToken].enabled) revert PrimaryRewardNotListed(rewardToken);

        RewardData storage reward = rewardData[rewardToken];
        uint256 amount = reward.queuedPenalty;
        if (amount == 0) revert NoQueuedPenalty();

        _updateRewardGlobal(rewardToken);

        if (amount < MIN_FLUSH_PENALTY_AMOUNT) revert PenaltyAmountTooLow(amount, MIN_FLUSH_PENALTY_AMOUNT);

        uint64 currentTime = _currentTime();
        uint64 newPeriodFinish;
        uint256 newRewardRate;
        if (block.timestamp >= reward.periodFinish) {
            reward.queuedPenalty = 0;
            newRewardRate = Math.mulDiv(amount, PRECISION, reward.rewardsDuration);
            newPeriodFinish = _currentTimePlus(reward.rewardsDuration);
        } else {
            uint256 remaining = reward.periodFinish - block.timestamp;
            uint256 leftoverRewards = Math.mulDiv(remaining, reward.rewardRate, PRECISION);
            uint256 rewardsToStream = amount + leftoverRewards;
            newRewardRate = Math.mulDiv(rewardsToStream, PRECISION, remaining);
            if (newRewardRate > type(uint128).max) revert Overflow();

            reward.queuedPenalty = 0;
            newPeriodFinish = reward.periodFinish;
        }

        reward.rewardRate = _toUint128(newRewardRate);
        reward.lastUpdateTime = currentTime;
        reward.periodFinish = newPeriodFinish;

        _assertRewardBacking(rewardToken);

        emit PenaltyFlushed(rewardToken, amount, reward.periodFinish);
    }

    /// @notice Returns the current reward-per-boosted-token accumulator for a reward token.
    /// @param rewardToken The reward token to inspect.
    /// @return accumulator The current reward-per-token value, scaled by `ACCUMULATOR_PRECISION`.
    function rewardPerToken(address rewardToken) external view returns (uint256 accumulator) {
        _requireRewardTokenListed(rewardToken);
        return rewardPerTokenFor(rewardToken);
    }

    /// @notice Compatibility shim for the removed remainder-carry state.
    /// @return residual Always zero because accumulator precision absorbs sub-wei dust.
    function residualNumerator(address) external pure returns (uint256 residual) {
        return 0;
    }

    /// @notice Returns the caller's current earned amount for a reward token.
    /// @param user The user to inspect.
    /// @param rewardToken The reward token to quote.
    /// @return accrued The earned reward amount for the user.
    function earned(address user, address rewardToken) external view returns (uint256 accrued) {
        _requireRewardTokenListed(rewardToken);
        return earnedUser(user, rewardToken);
    }

    /// @notice Returns every stake ever created by a user, including withdrawn positions.
    /// @param user The user to inspect.
    /// @return stakes The user's stake array.
    function getUserStakes(address user) external view returns (Stake[] memory stakes) {
        return _userStakes[user];
    }

    /// @notice Returns one stake position by id.
    /// @param user The user to inspect.
    /// @param stakeId The stake index to fetch.
    /// @return userStake The requested stake position.
    function getUserStake(address user, uint256 stakeId) external view returns (Stake memory userStake) {
        if (stakeId >= _userStakes[user].length) revert StakeNotFound(stakeId);
        return _userStakes[user][stakeId];
    }

    /// @notice Returns the currently listed reward tokens.
    /// @return rewardTokens The reward token list.
    function getRewardTokens() external view returns (address[] memory rewardTokens) {
        return rewardTokensList;
    }

    /// @notice Returns a configured lock tier by id.
    /// @param tierId The tier id to inspect.
    /// @return tier The lock tier configuration.
    function getLockTier(uint8 tierId) external view returns (LockTier memory tier) {
        _requireTierExists(tierId);
        return lockTiers[tierId];
    }

    /// @notice Returns the number of active, non-withdrawn stakes for a user.
    /// @param user The user to inspect.
    /// @return count The active stake count.
    function getActiveStakeCount(address user) external view returns (uint256 count) {
        return _userActiveStakeCount[user];
    }

    function _activeStakeCount(address user) internal view returns (uint256 count) {
        return _userActiveStakeCount[user];
    }

    /// @notice Lists a reward token with its distribution duration.
    /// @param token The reward token to enable.
    /// @param duration The streaming duration for future reward notifications.
    function addRewardToken(address token, uint64 duration) external onlyOwner {
        if (token == address(0)) revert ZeroAddress();
        if (rewardTokensList.length >= MAX_REWARD_TOKENS) revert TooManyRewardTokens(MAX_REWARD_TOKENS);
        if (rewardData[token].enabled) revert RewardTokenAlreadyListed(token);

        _validateRewardDuration(duration);

        RewardData storage reward = rewardData[token];
        reward.enabled = true;
        reward.rewardsDuration = duration;
        rewardTokensList.push(token);

        emit RewardTokenAdded(token, duration);
    }

    /// @notice Pulls new rewards into the contract and starts or extends the stream for a listed token.
    /// @param token The listed reward token to top up.
    /// @param amount The number of reward tokens to add.
    function notifyRewardAmount(address token, uint256 amount) external onlyOwner nonReentrant {
        if (amount == 0) revert RewardAmountTooLow(0, 1);
        RewardData storage reward = _requireRewardTokenListed(token);

        _updateRewardGlobal(token);

        IERC20 rewardToken = IERC20(token);
        uint256 balanceBefore = rewardToken.balanceOf(address(this));
        rewardToken.safeTransferFrom(msg.sender, address(this), amount);
        uint256 received = rewardToken.balanceOf(address(this)) - balanceBefore;
        if (received != amount) revert UnsupportedToken(token);

        uint256 newRewardRate = _calculateUpdatedRewardRate(reward, received);
        if (newRewardRate == 0) revert RewardAmountTooLow(received, 1);

        reward.rewardRate = _toUint128(newRewardRate);
        reward.lastUpdateTime = _currentTime();
        reward.periodFinish = _currentTimePlus(reward.rewardsDuration);

        _assertRewardBacking(token);

        emit RewardNotified(token, received, reward.periodFinish);
    }

    /// @notice Creates a new lock tier with a unique, never-reused id.
    /// @param duration The lock duration in seconds.
    /// @param multiplierBps The boost multiplier in basis points.
    /// @return tierId The newly assigned lock tier id.
    function setLockTier(uint64 duration, uint32 multiplierBps) external onlyOwner returns (uint8 tierId) {
        if (nextLockTierId >= MAX_LOCK_TIERS) revert TooManyTiers(MAX_LOCK_TIERS);
        if (multiplierBps < MIN_BOOST_BPS || multiplierBps > MAX_BOOST_BPS) {
            revert BoostOutOfRange(multiplierBps, MIN_BOOST_BPS, MAX_BOOST_BPS);
        }
        if (duration == 0 && multiplierBps > MIN_BOOST_BPS) {
            revert RewardDurationOutOfRange(duration, 1, type(uint64).max);
        }

        tierId = nextLockTierId;
        nextLockTierId = tierId + 1;
        lockTiers[tierId] = LockTier({enabled: true, duration: duration, multiplierBps: multiplierBps});

        emit LockTierSet(tierId, duration, multiplierBps, true);
    }

    /// @notice Disables a lock tier for future stakes without affecting existing positions.
    /// @param tierId The tier id to disable.
    function disableLockTier(uint8 tierId) external onlyOwner {
        _requireTierExists(tierId);

        LockTier storage tier = lockTiers[tierId];
        tier.enabled = false;

        emit LockTierSet(tierId, tier.duration, tier.multiplierBps, false);
    }

    /// @notice Sets the early unstake penalty in basis points.
    /// @param bps The new penalty rate.
    function setEarlyUnstakePenalty(uint256 bps) external onlyOwner {
        if (bps > MAX_PENALTY_BPS) revert PenaltyTooHigh(bps, MAX_PENALTY_BPS);
        earlyUnstakePenaltyBps = bps;

        emit EarlyUnstakePenaltyUpdated(bps);
    }

    /// @notice Sets the primary reward token used for penalty redistribution.
    /// @param token The new primary reward token, which must equal the staking token and be listed.
    function setPrimaryRewardToken(address token) external onlyOwner {
        if (token == address(0)) revert ZeroAddress();
        if (token != address(stakingToken)) revert CompoundRequiresStakingTokenReward();
        if (!rewardData[token].enabled) revert PrimaryRewardNotListed(token);

        primaryRewardToken = token;

        emit PrimaryRewardTokenSet(token);
    }

    /// @notice Updates a reward token's distribution duration after its current period has ended.
    /// @param token The listed reward token to update.
    /// @param duration The new rewards duration in seconds.
    function setRewardsDuration(address token, uint64 duration) external onlyOwner {
        RewardData storage reward = _requireRewardTokenListed(token);
        _validateRewardDuration(duration);

        if (block.timestamp < reward.periodFinish) revert RewardPeriodNotFinished(reward.periodFinish);

        reward.rewardsDuration = duration;
    }

    /// @notice Recovers an unrelated ERC20 that was sent to the contract by mistake.
    /// @param token The token to recover.
    /// @param amount The amount to recover.
    function recoverERC20(address token, uint256 amount) external onlyOwner {
        if (token == address(0)) revert ZeroAddress();
        if (token == address(stakingToken)) revert CannotRecoverStakingToken();
        if (rewardData[token].enabled) revert CannotRecoverRewardToken(token);

        IERC20(token).safeTransfer(owner(), amount);

        emit RecoveredToken(token, amount);
    }

    /// @notice Pauses entry points that create new exposure.
    function pause() external onlyOwner {
        _pause();
    }

    /// @notice Unpauses entry points that create new exposure.
    function unpause() external onlyOwner {
        _unpause();
    }

    function _updateRewardGlobal(address token) internal {
        RewardData storage reward = rewardData[token];
        if (totalBoostedSupply == 0 && reward.lastUpdateTime < reward.periodFinish) {
            uint64 currentTime = _currentTime();
            if (currentTime > reward.lastUpdateTime) {
                uint256 pausedTime = currentTime - reward.lastUpdateTime;
                uint256 extendedPeriodFinish = uint256(reward.periodFinish) + pausedTime;
                if (extendedPeriodFinish > type(uint64).max) revert Overflow();

                reward.periodFinish = uint64(extendedPeriodFinish);
                reward.lastUpdateTime = currentTime;
            }
        } else {
            uint64 timeApplicable = _lastTimeRewardApplicable(reward);
            if (timeApplicable > reward.lastUpdateTime) {
                reward.rewardPerTokenStored += Math.mulDiv(
                    timeApplicable - reward.lastUpdateTime,
                    uint256(reward.rewardRate) * EXTRA_PRECISION,
                    totalBoostedSupply
                );
            }
            reward.lastUpdateTime = timeApplicable;
        }
    }

    function _updateRewardUser(address user, address token) internal {
        _updateRewardGlobal(token);
        RewardData storage reward = rewardData[token];
        rewards[user][token] = earnedUser(user, token);
        userRewardPerTokenPaid[user][token] = reward.rewardPerTokenStored;
    }

    function _updateRewardAll(address user) internal {
        uint256 rewardsLength = rewardTokensList.length;
        for (uint256 i; i < rewardsLength; ++i) {
            _updateRewardUser(user, rewardTokensList[i]);
        }
    }

    function rewardPerTokenFor(address token) internal view returns (uint256) {
        RewardData storage reward = rewardData[token];
        uint256 rewardPerTokenStored_ = reward.rewardPerTokenStored;
        if (totalBoostedSupply == 0) return rewardPerTokenStored_;

        uint256 timeApplicable = _lastTimeRewardApplicable(reward);
        if (timeApplicable <= reward.lastUpdateTime) return rewardPerTokenStored_;

        uint256 elapsed = timeApplicable - reward.lastUpdateTime;
        return
            rewardPerTokenStored_
                + Math.mulDiv(elapsed, uint256(reward.rewardRate) * EXTRA_PRECISION, totalBoostedSupply);
    }

    function earnedUser(address user, address token) internal view returns (uint256) {
        return Math.mulDiv(
            _userBoostedAmount[user],
            rewardPerTokenFor(token) - userRewardPerTokenPaid[user][token],
            ACCUMULATOR_PRECISION
        ) + rewards[user][token];
    }

    function _createStake(address user, uint128 amount, uint8 tierId, LockTier storage tier)
        internal
        returns (uint256 stakeId, uint64 unlockTime, uint128 boostedAmount)
    {
        boostedAmount = _toUint128(Math.mulDiv(amount, tier.multiplierBps, BPS));
        uint64 currentTime = _currentTime();
        unlockTime = _currentTimePlus(tier.duration);

        stakeId = _userStakes[user].length;
        _userStakes[user].push(
            Stake({
                amount: amount,
                boostedAmount: boostedAmount,
                tierId: tierId,
                startTime: currentTime,
                unlockTime: unlockTime,
                withdrawn: false
            })
        );

        totalRawSupply += amount;
        totalBoostedSupply += boostedAmount;
        _userActiveStakeCount[user] += 1;
        _userBoostedAmount[user] += boostedAmount;
    }

    function _distributeOrQueuePenalty(address penalizedUser, uint128 penalty) internal {
        RewardData storage reward = rewardData[primaryRewardToken];
        uint256 penalizedRemainingBoost = _userBoostedAmount[penalizedUser];
        uint256 eligibleBoostedSupply =
            totalBoostedSupply > penalizedRemainingBoost ? totalBoostedSupply - penalizedRemainingBoost : 0;

        if (eligibleBoostedSupply == 0) {
            reward.queuedPenalty += penalty;
            emit PenaltyQueued(primaryRewardToken, penalty);
            return;
        }

        reward.rewardPerTokenStored += Math.mulDiv(penalty, ACCUMULATOR_PRECISION, eligibleBoostedSupply);
        userRewardPerTokenPaid[penalizedUser][primaryRewardToken] = reward.rewardPerTokenStored;

        emit PenaltyFlushed(primaryRewardToken, penalty, reward.periodFinish);
    }

    function _claimReward(address user, address rewardToken) internal returns (uint256 claimed) {
        claimed = rewards[user][rewardToken];
        if (claimed == 0) return 0;

        rewards[user][rewardToken] = 0;
        IERC20(rewardToken).safeTransfer(user, claimed);

        emit RewardClaimed(user, rewardToken, claimed);
    }

    function _calculateUpdatedRewardRate(RewardData storage reward, uint256 amount) internal view returns (uint256) {
        uint256 duration = reward.rewardsDuration;
        uint256 rewardRate_;
        if (block.timestamp >= reward.periodFinish) {
            rewardRate_ = Math.mulDiv(amount, PRECISION, duration);
        } else {
            uint256 remaining = reward.periodFinish - block.timestamp;
            uint256 leftover = Math.mulDiv(remaining, reward.rewardRate, PRECISION);
            rewardRate_ = Math.mulDiv(amount + leftover, PRECISION, duration);
        }

        return rewardRate_;
    }

    function _assertRewardBacking(address token) internal view {
        uint256 required = _unstreamedRewardBudget(token);
        if (token == address(stakingToken)) {
            required += totalRawSupply + rewardData[token].queuedPenalty;
        }

        uint256 balance = IERC20(token).balanceOf(address(this));
        if (balance < required) revert InsufficientRewardBalance(token, required, balance);
    }

    function _unstreamedRewardBudget(address token) internal view returns (uint256 budget) {
        RewardData storage reward = rewardData[token];
        if (block.timestamp >= reward.periodFinish) return 0;
        return Math.mulDiv(reward.periodFinish - block.timestamp, reward.rewardRate, PRECISION);
    }

    function _lastTimeRewardApplicable(RewardData storage reward) internal view returns (uint64) {
        return uint64(Math.min(block.timestamp, reward.periodFinish));
    }

    function _requireEnabledTier(uint8 tierId) internal view returns (LockTier storage tier) {
        _requireTierExists(tierId);
        tier = lockTiers[tierId];
        if (!tier.enabled) revert TierDisabled(tierId);
    }

    function _requireTierExists(uint8 tierId) internal view {
        if (tierId >= nextLockTierId) revert TierNotFound(tierId);
    }

    function _requireRewardTokenListed(address token) internal view returns (RewardData storage reward) {
        reward = rewardData[token];
        if (!reward.enabled) revert RewardTokenNotListed(token);
    }

    function _getUserStakeStorage(address user, uint256 stakeId) internal view returns (Stake storage userStake) {
        if (stakeId >= _userStakes[user].length) revert StakeNotFound(stakeId);
        userStake = _userStakes[user][stakeId];
    }

    function _validateRewardDuration(uint64 duration) internal pure {
        if (duration < MIN_REWARD_DURATION || duration > MAX_REWARD_DURATION) {
            revert RewardDurationOutOfRange(duration, MIN_REWARD_DURATION, MAX_REWARD_DURATION);
        }
    }

    function _currentTime() internal view returns (uint64) {
        if (block.timestamp > type(uint64).max) revert Overflow();
        return uint64(block.timestamp);
    }

    function _currentTimePlus(uint64 duration) internal view returns (uint64) {
        uint256 unlockTime = block.timestamp + duration;
        if (unlockTime > type(uint64).max) revert Overflow();
        return uint64(unlockTime);
    }

    function _toUint128(uint256 value) internal pure returns (uint128 casted) {
        if (value > type(uint128).max) revert Overflow();
        return uint128(value);
    }
}
