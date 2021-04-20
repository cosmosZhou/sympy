from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
def apply(given, s=None):
    assert given.is_NotContains    
    
    e, S = given.args
    assert S.is_Union
    if s is None:
        s = S.args[0]
    else:
        assert s in S.args
    
    return NotContains(e, s)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(NotContains(x, A | B))
    
    Eq << sets.notcontains.imply.et.split.union.apply(Eq[0], simplify=None)
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])
    
if __name__ == '__main__':
    prove()

