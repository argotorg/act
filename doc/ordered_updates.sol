pragma solidity >=0.8.0;

contract Admins {
    address public admin1;
    address public admin2;

    constructor(address _admin1) {
        admin1 = _admin1;
        admin2 = tx.origin;
    }

    function set_admin2(address new_admin2){
        admin2 = new_admin2;
    }

}

contract Asset {
    uint256 public value;
    Admins admins;
    mapping (address => uint256) public balanceOf;

    constructor(uint256 _value) {
        value = _value;
        admins = Admins(msg.sender);
        balanceOf[address(this)] = _value;
    }

    function assetTransfer(uint256 amt, address to) public returns (bool) {
        require (msg.sender == admins.admin1 || msg.sender == admins.admin2);

        balanceOf[address(this)] = balanceOf[address(this)] - amt;
        balanceOf[to] = balanceOf[to] + amt;

        return true;
    }

    function setAdmins(address new_admin1, address new_admin2) public {
        if (msg.sender == admins.admin1 || msg.sender == admins.admin2) {
            admins = Admins(new_admin1);
            admins.admin2 = new_admin2;
        }
    }
}