contract A {
  int128 x;
  int128 y;

  constructor() {
    x = 0;
    y = 0;
  }

  function f() public returns(int128) {
    return x % y;
  }
}
