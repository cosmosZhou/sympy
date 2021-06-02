from util import *
# given: x != y
# x not in {y}


@apply
def apply(given):
    assert given.is_Unequal
    x, y = given.args
    return Contains(x, y.universalSet // {y})


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Unequal(x, y))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].simplify()
    
    Eq <<= Eq[-1] & Eq[0]    
    

if __name__ == '__main__':
    run()

