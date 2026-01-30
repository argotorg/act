
x : int192
y : int192

@deploy
def __init__():
  self.x = 0
  self.y = 0

@external
def f() -> int192:
  return self.x * self.y
