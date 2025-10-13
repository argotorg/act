#interface Token 
#  function balanceOf(address) external view returns (uint256);
#  function transferFrom(address from, address to, uint256 value) external returns (uint);
#}
interface Token:
  def balanceOf(of: address) -> uint256: view
  def transferFrom(_from: address, _to: address, _value: uint256) -> uint256: nonpayable

token0 : Token
token1 : Token

@deploy
def __init__(t0: address, t1: address):
  assert (t0 != t1)
  self.token0 = Token(t0)
  self.token1 = Token(t1)

@external
def swap0(amt: uint256) -> uint256:
  reserve0 : uint256 = staticcall self.token0.balanceOf(self)
  reserve1 : uint256 = staticcall self.token1.balanceOf(self)

  extcall self.token0.transferFrom(msg.sender, self, amt)
  extcall self.token1.transferFrom(self, msg.sender, (reserve1*amt)//(reserve0+amt))

  return 1

@external
def swap1(amt: uint256) -> uint256:
  reserve0 : uint256 = staticcall self.token0.balanceOf(self)
  reserve1 : uint256 = staticcall self.token1.balanceOf(self)

  extcall self.token1.transferFrom(msg.sender, self, amt)
  extcall self.token0.transferFrom(self, msg.sender, (reserve1*amt)//(reserve0+amt))

  return 1
