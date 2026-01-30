contract A {
  int192 x;
  int192 y;

  constructor() {
    x = 0;
    y = 0;
  }

  function f() public returns(int192) {
    return x / y;
  }
}
