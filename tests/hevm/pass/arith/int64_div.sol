contract A {
  int64 x;
  int64 y;

  constructor() {
    x = 0;
    y = 0;
  }

  function f() public returns(int64) {
    return x / y;
  }
}
