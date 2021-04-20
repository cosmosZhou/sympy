from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(given):
    notcontains, *limits = axiom.forall_notcontains(given)
    
    e, B = axiom.limit_is_set(limits)    
    _e, A = notcontains.args
    assert e == _e
    
    return Equal(A & B, e.emptySet)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(ForAll[x: A](NotContains(x, B)))
    
    Eq << algebra.forall.imply.ou.apply(Eq[0], simplify=False)    
    
    Eq << ~Eq[-1]
    
    Eq << ~Eq[1]

    
if __name__ == '__main__':
    prove()

