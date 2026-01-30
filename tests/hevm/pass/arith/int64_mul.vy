
x : int64
y : int64

@deploy
def __init__():
  self.x = 0
  self.y = 0

@external
def f() -> int64:
  return self.x * self.y
