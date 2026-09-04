pragma solidity >=0.8.0;

contract Admins {
    address public admin1;
    address public admin2;

    constructor(address _admin1, address _admin2) {
        admin1 = _admin1;
        admin2 = _admin2;
    }

}

contract Asset {
    Admins admins;
    mapping (address => uint256) public balanceOf;

    constructor(uint256 _value) {
        admins = new Admins(msg.sender, tx.origin);
        balanceOf[address(this)] = _value;
    }

    function assetTransfer(uint256 amt, address recipient) public returns (bool) {
        require (msg.sender == admins.admin1() || msg.sender == admins.admin2());

        balanceOf[address(this)] = balanceOf[address(this)] - amt;
        balanceOf[recipient] = balanceOf[recipient] + amt;

        return true;
    }

    function setAdmins(address new_admin1, address new_admin2) public {
        if (msg.sender == admins.admin1() || msg.sender == admins.admin2()) {
            admins = new Admins(new_admin1, new_admin2);
        }
    }
}
