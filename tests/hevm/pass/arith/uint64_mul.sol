contract A {
  uint64 x;
  uint64 y;

  constructor() {
    x = 0;
    y = 0;
  }

  function f() public returns(uint64) {
    return x * y;
  }
}
