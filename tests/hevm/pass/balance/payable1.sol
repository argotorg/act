// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract PayableVault {
    mapping(address => uint256) credit;
    uint256 totalCredit;

    constructor() {
        totalCredit = 0;
    }

    function deposit() external payable returns (uint256) {
        require(msg.value > 0, "CALLVALUE=0");
        credit[msg.sender] += msg.value;
        totalCredit += msg.value;

        return credit[msg.sender];
    }

    function solvency() external view returns (bool) {
        // Matches your Act return: BALANCE >= totalCredit
        return (address(this).balance >= totalCredit);
    }
}
