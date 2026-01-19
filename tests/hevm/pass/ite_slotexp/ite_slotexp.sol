contract A {
  uint x = 0;
  uint y = 0;

  function f(uint a, uint b) public {
    require(x < 100,"");
    require(y < 100,"");
    x = ((b>3) ? x : y) + ((a>2) ? 42 : 17);
    require(x < 30, "");
  }
}


