from util import *

import axiom


@apply
def apply(imply):
    assert imply.is_Contains
    
    x, intersection = imply.of(Contains)
    
    ss = intersection.of(Intersection)
    
    return And(*(Contains(x, s) for s in ss))


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Contains(x, A & B))
    
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

