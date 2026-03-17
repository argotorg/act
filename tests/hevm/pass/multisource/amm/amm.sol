pragma solidity >=0.8.0;

contract Token {
    uint256 public totalSupply;
    mapping (address => uint256) public balanceOf;
    mapping (address => mapping (address => uint256)) public allowance;

    constructor(uint256 _totalSupply) {
        totalSupply = _totalSupply;
        balanceOf[msg.sender] = _totalSupply;
    }


    function approve(address spender, uint256 value) public returns (bool) {
        if(spender != msg.sender) {
            allowance[msg.sender][spender] = value;
        }
        return true;
    }

    function transfer(uint256 value, address to) public returns (bool) {
        balanceOf[msg.sender] = balanceOf[msg.sender] - value;
        balanceOf[to] = balanceOf[to] + value;
        return true;
    }

    function transferFrom(address from, address to, uint256 value) public returns (bool) {
        if(from != msg.sender && allowance[from][msg.sender] != type(uint256).max) {
            allowance[from][msg.sender] = allowance[from][msg.sender] - value;
        }
        balanceOf[from] = balanceOf[from] - value;
        balanceOf[to] = balanceOf[to] + value;
        return true;
    }
}


contract Amm is Token {
    uint256 internal constant MINIMUM_LIQUIDITY = 1000;
    Token token0;
    Token token1;
    uint256 reserve0;
    uint256 reserve1;

    constructor(address t0, address t1, uint256 liquidity) Token(liquidity - MINIMUM_LIQUIDITY) {
        require (t0 != t1);
        token0 = Token(t0);
        token1 = Token(t1);

        require(liquidity*liquidity == token0.balanceOf(address(this)) * token1.balanceOf(address(this)), "Invalid initial liquidity");
        require(liquidity > 0, 'Invalid initial liquidity');
        totalSupply = liquidity;
        balanceOf[address(this)] =  MINIMUM_LIQUIDITY;
        balanceOf[msg.sender] = liquidity - MINIMUM_LIQUIDITY;
        reserve0 = token0.balanceOf(address(this));
        reserve1 = token1.balanceOf(address(this));
    }

    function mint(address to) public returns (uint256 liquidity) {
      require(totalSupply != 0);

      uint256 balance0 = token0.balanceOf(address(this));
      uint256 balance1 = token1.balanceOf(address(this));

      uint256 amount0 = balance0 - reserve0;
      uint256 amount1 = balance1 - reserve1;

      uint256 liq0 = amount0 * totalSupply / reserve0;
      uint256 liq1 = amount1 * totalSupply / reserve1;

      if (liq0 <= liq1) {
        liquidity = liq0;
      } else {
        liquidity = liq1;
      }

      require(liquidity != 0, "Insufficient liquidity");
      totalSupply += liquidity;
      balanceOf[to] += liquidity;

      reserve0 = balance0;
      reserve1 = balance1;
    }

    function burn(uint256 liquidity, address to) public {
      require(totalSupply != 0);

      uint256 amount0 = (liquidity * reserve0) / totalSupply;
      uint256 amount1 = (liquidity * reserve1) / totalSupply;

      totalSupply -= liquidity;
      balanceOf[msg.sender] -= liquidity;

      token0.transfer(amount0, to);
      token1.transfer(amount1, to);

      reserve0 = token0.balanceOf(address(this));
      reserve1 = token1.balanceOf(address(this));
    }

    function swap0(uint256 amount1Out, address to) public {
      require(amount1Out > 0, 'Insufficient output amount');
      require(amount1Out < reserve1, 'Insufficient liquidity');
      require(to != address(token0) && to != address(token1), 'Invalid TO');

      token1.transfer(amount1Out, to);

      uint256 balance0 = token0.balanceOf(address(this));
      uint256 balance1 = token1.balanceOf(address(this));

      require(balance0 > reserve0, 'Insufficient input amount');
      uint256 amount0In = balance0 - reserve0;

      require(amount1Out <= (reserve1 * amount0In / (reserve0 + amount0In)), 'K');

      reserve0 = balance0;
      reserve1 = balance1;
    }

    function swap1(uint256 amount0Out, address to) public {
      require(amount0Out > 0, 'Insufficient output amount');
      require(amount0Out < reserve0, 'Insufficient liquidity');
      require(to != address(token0) && to != address(token1), 'Invalid TO');

      token0.transfer(amount0Out, to);

      uint256 balance0 = token0.balanceOf(address(this));
      uint256 balance1 = token1.balanceOf(address(this));

      require(balance1 > reserve1, 'Insufficient input amount');
      uint256 amount1In = balance1 - reserve1;

      require(amount0Out <= (reserve0 * amount1In / (reserve1 + amount1In)), 'K');

      reserve0 = balance0;
      reserve1 = balance1;
    }
}
