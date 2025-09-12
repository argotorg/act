pragma solidity >=0.8.0;

contract A {
    uint z;

    constructor(uint _z) {
        z = _z;
    }

    function setz(uint _z) public {
        z = _z;
    }
}


contract B {
    uint x;
    A a;
    
    constructor(uint x1) {
        x = x1;
        a = new A(42);
    }

    function foo() public {
        a = new A(8);
        a.setz(11);
    }
}
