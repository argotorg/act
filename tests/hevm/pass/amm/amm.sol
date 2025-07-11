pragma solidity >=0.8.0;

contract Token {
    mapping (address => uint) public balanceOf;

    constructor(uint _totalSupply) {
        balanceOf[msg.sender] = _totalSupply;
    }


    function transferFrom(uint256 value, address from, address to) public returns (uint) {
        balanceOf[from] = balanceOf[from] - value;
        balanceOf[to] = balanceOf[to] + value;
        return 1;
    }

}


contract Amm {

    Token token0;
    Token token1;

    constructor(address t0, address t1) {
        require (t0 != t1);
        token0 = Token(t0);
        token1 = Token(t1);
    }

    function swap0(uint256 amt) public returns (uint) {
        uint256 reserve0 = token0.balanceOf(address(this));
        uint256 reserve1 = token1.balanceOf(address(this));

        token0.transferFrom(amt, msg.sender, address(this));
        token1.transferFrom((reserve1*amt)/(reserve0+amt), address(this), msg.sender);

        return 1;
    }

    function swap1(uint256 amt) public returns (uint) {
        uint256 reserve0 = token0.balanceOf(address(this));
        uint256 reserve1 = token1.balanceOf(address(this));

        token1.transferFrom(amt, msg.sender, address(this));
        token0.transferFrom((reserve0*amt)/(reserve1+amt), address(this), msg.sender);

        return 1;
    }

}
