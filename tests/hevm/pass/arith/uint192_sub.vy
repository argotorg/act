
x : uint192
y : uint192

@deploy
def __init__():
  self.x = 0
  self.y = 0

@external
def f() -> uint192:
  return self.x - self.y
