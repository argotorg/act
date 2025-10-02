pragma solidity >=0.8.0;

interface Token {
  function balanceOf(address) external view returns (uint256);
  function transferFrom(address from, address to, uint256 value) external returns (uint);
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

        token0.transferFrom(msg.sender, address(this), amt);
        token1.transferFrom(address(this), msg.sender, (reserve1*amt)/(reserve0+amt));

        return 1;
    }

    function swap1(uint256 amt) public returns (uint) {
        uint256 reserve0 = token0.balanceOf(address(this));
        uint256 reserve1 = token1.balanceOf(address(this));

        token1.transferFrom(msg.sender, address(this), amt);
        token0.transferFrom(address(this), msg.sender, (reserve0*amt)/(reserve1+amt));

        return 1;
    }

}
