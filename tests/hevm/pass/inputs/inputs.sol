pragma solidity >=0.8.0;

contract Inputs {

    constructor() {}
       
    function test(uint128 x) public returns (uint128) {
	require(x>0);
	return (x+1); 
    }
}
