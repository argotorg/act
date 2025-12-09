# @version ^0.4.0

totalSupply: public(uint256)
balanceOf: public(HashMap[address, uint256])
allowance: public(HashMap[address, HashMap[address, uint256]])

@deploy
def __init__(_totalSupply: uint256):
  self.totalSupply = _totalSupply
  self.balanceOf[msg.sender] = _totalSupply

@external
def approve(spender: address, value_: uint256) -> bool:
  if spender != msg.sender:
    self.allowance[msg.sender][spender] = value_
  return True

@external
def transfer(value_: uint256, to: address) -> bool:
  self.balanceOf[msg.sender] = self.balanceOf[msg.sender] - value_
  self.balanceOf[to] = self.balanceOf[to] + value_
  return True

@external
def transferFrom(from_: address, to: address, value_: uint256) -> bool:
  if from_ != msg.sender and self.allowance[from_][msg.sender] != max_value(uint256):
    self.allowance[from_][msg.sender] = self.allowance[from_][msg.sender] - value_
  self.balanceOf[from_] = self.balanceOf[from_] - value_
  self.balanceOf[to] = self.balanceOf[to] + value_
  return True

@external
def burn(value_: uint256) -> bool:
  self.totalSupply -= value_
  self.balanceOf[msg.sender] = self.balanceOf[msg.sender] - value_
  return True

@external
def burnFrom(account: address, value_: uint256) -> bool:
  if account != msg.sender and self.allowance[account][msg.sender] != max_value(uint256):
    self.allowance[account][msg.sender] -= value_
  self.totalSupply -= value_
  self.balanceOf[account] -= value_
  return True

@external
def mint(account: address, value_: uint256) -> bool:
  self.totalSupply += value_
  self.balanceOf[account] += value_
  return True

