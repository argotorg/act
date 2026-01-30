
x : uint256
y : uint256

@deploy
def __init__():
  self.x = 0
  self.y = 0

@external
def f() -> uint256:
  return self.x * self.y
