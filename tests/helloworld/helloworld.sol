// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract HelloWorld {
    mapping(address => uint256) public hello;
    
    constructor() {
        hello[msg.sender] = 42;
    }
    
   
    function setHello(uint256 value, address to) public returns (uint256) {
        hello[to] = value;
    
        return 1;
    }
    

}
