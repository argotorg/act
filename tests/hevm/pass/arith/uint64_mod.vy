
x : uint64
y : uint64

@deploy
def __init__():
  self.x = 0
  self.y = 0

@external
def f() -> uint64:
  return self.x % self.y
