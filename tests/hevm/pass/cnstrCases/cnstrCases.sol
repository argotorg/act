contract A {
  uint s;

  constructor(uint x) {
    s = (x > 4) ? x+42 : x+17;
  }
}

contract B {
  A a;

  constructor(uint w) {
    a = new A(w);
  }
}
