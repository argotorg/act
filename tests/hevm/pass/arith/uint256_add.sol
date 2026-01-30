contract A {
  uint256 x;
  uint256 y;

  constructor() {
    x = 0;
    y = 0;
  }

  function f() public returns(uint256) {
    return x + y;
  }
}
