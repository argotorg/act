
x: uint128

@deploy
def __init__():
  self.x = 0

@external
def setx(a: uint128):
  self.x = a
