
x : int128
y : int128

@deploy
def __init__():
  self.x = 0
  self.y = 0

@external
def f() -> int128:
  return self.x // self.y
