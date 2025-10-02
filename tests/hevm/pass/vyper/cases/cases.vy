# @version ^0.4.0

x: uint128
m: HashMap[uint128, uint128]

@deploy
def __init__():
    self.x = 0

@external
def f():
    if self.x > 2:
        self.x = self.m[2]
    else:
        if 1 <= self.x and self.x <= 2:
            self.x = self.m[3]
        else:
            self.x = self.m[self.x]
