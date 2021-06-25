from util import *


@apply
def apply(imply):
    assert imply.is_Contains
    x = imply.generate_var(**imply.lhs.type.dict)
    
    return Any[x:imply.rhs](Equal(imply.lhs, x))


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Contains(x, S))
    
    Eq << Eq[1].simplify()
    
if __name__ == '__main__':
    run()

