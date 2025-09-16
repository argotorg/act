pragma solidity >=0.8.0;

contract A {
    uint public x;

    constructor (uint z)  {
        x = z;
    }

    function set_x(uint z) public{
        x = z;
    }
}

contract B {
    A a;

    constructor(address x) {
        a = A(x);
    }

    function upd() public {
        a.set_x(42);
    }

}

contract C {
    A a;
    B b1;
    B b2;

    constructor(address x) {
        a = new A(11);
        b1 = new B(x);
        b2 = new B(x);
    }
}
