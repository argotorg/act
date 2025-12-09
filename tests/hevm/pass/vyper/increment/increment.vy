x : uint128

@deploy
def __init__():
  self.x = 0

@external
def f():
  self.x = self.x + 1
