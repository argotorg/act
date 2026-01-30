// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract A {
    constructor() payable {
    }

    function deposit() external payable {
    }

}

contract B {
    A av;

    constructor() payable {
        require(msg.value >= 42);
        av = new A{value: 42}();
    }
    function newA(uint256 amt) external {
        require(amt <= address(this).balance, "amt > BALANCE");

        av = new A{value: amt}();
    }
}

