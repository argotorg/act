m: public(HashMap[uint64, HashMap[uint128, uint32]])

@deploy
def __init__(a: uint64, b: uint128, c: uint32):
  self.m[a][b] = c

@external
def setm(a: uint64, b: uint128, c: uint32):
  self.m[a][b] = c
  
