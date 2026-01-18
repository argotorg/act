contract A {
  uint s;
  uint a;
  uint b;

  constructor(uint x, uint y, uint z) {
    if (x > 4) {
      require(y < z, "");
      s = y;
    } else {
      require(y > z, "");
      s = z;
    }
  }
}

contract B {
  A a;
  uint x;

  constructor(uint w, uint u, uint v) {
    a = (w > 67) ? new A(u, v, w) : new A(v, u, w);
  }

  function foo(uint y) public {
    a = new A(y+5, y, y+1);
  }
}

contract C {
  B b;

  constructor(uint z) {
    require(z<=4, "");
    b = new B(z,z+1,z);
  }
}
    
