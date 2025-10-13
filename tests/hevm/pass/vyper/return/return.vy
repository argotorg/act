x: uint128

@deploy
def __init__():
  self.x = 0

@external
def f() -> uint128:
  return self.x
