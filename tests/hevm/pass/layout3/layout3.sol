contract Map {
    uint128 public val;
    mapping (uint => uint128) public f;
    //mapping (uint => uint256) public f;
    
    constructor() {
        val = 11;
        f[11] = 42;
    }

    //function set(uint256 value, uint key) external returns (uint) {
    function set(uint128 value, uint key) external returns (uint) {
        f[key] = value;
        return 1;
    }
}
