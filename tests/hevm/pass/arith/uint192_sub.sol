contract A {
  uint192 x;
  uint192 y;

  constructor() {
    x = 0;
    y = 0;
  }

  function f() public returns(uint192) {
    return x - y;
  }
}
