contract A {
  uint128 x;
  uint128 y;

  constructor() {
    x = 0;
    y = 0;
  }

  function f() public returns(uint128) {
    return x * y;
  }
}
