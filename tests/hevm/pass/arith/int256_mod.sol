contract A {
  int256 x;
  int256 y;

  constructor() {
    x = 0;
    y = 0;
  }

  function f() public returns(int256) {
    return x % y;
  }
}
