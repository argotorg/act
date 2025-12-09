interface A1:
  def setx(n: uint128): nonpayable

a: A1

@deploy
def __init__(c: address):
  self.a = A1(c)

@external
def setA1x(n: uint128):
  extcall self.a.setx(n)
