
x : int256
y : int256

@deploy
def __init__():
  self.x = 0
  self.y = 0

@external
def f() -> int256:
  return self.x - self.y
