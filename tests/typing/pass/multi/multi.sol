pragma solidity >=0.8.0;

contract A {
    uint public x;

    constructor (uint z)  {
	x = z;
    }

    function set_x(uint z) public {
	x = z;
    }
}

contract B {

    uint public y;
    A public a;

    constructor() {
	y = 0;
	a = new A(0);
    }

    function remote(uint z) public {
	a.set_x(z);
    }

    function multi(uint z) public {
	y = 1;
	a.set_x(z);
    }
}
