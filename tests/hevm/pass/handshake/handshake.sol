// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract TwoPartyAgreement {

    address proposer;
    address counterparty;
    uint256 state;

    constructor(address _counterparty) {
        proposer = msg.sender;
        counterparty = _counterparty;
        state = 0; // 0: Proposed, 1: Accepted, 2: Executed, 3: Cancelled
    }

    modifier onlyProposer() {
        require(msg.sender == proposer, "Only proposer");
        _;
    }

    modifier onlyCounterparty() {
        require(msg.sender == counterparty, "Only counterparty");
        _;
    }

    modifier inState(uint256 _state) {
        require(state == _state, "Invalid state");
        _;
    }

    function accept() external onlyCounterparty inState(0) {
        state = 1; // Accepted
    }

    function execute() external onlyProposer inState(1) {
        state = 2; // Executed
    }

    function cancel() external onlyProposer inState(0) {
        state = 3;  // Cancelled
    }
}
