from axiom.utility import prove, apply
from sympy import *
from axiom import algebra, sets
import axiom


@apply
def apply(given, index=-1):
    function, *limits = axiom.is_ForAll(given)

    assert len(limits) > 1
    del limits[index]
    
    return ForAll(function, *limits)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    f = Function.f(integer=True)

    Eq << apply(ForAll[x:A, y:B](f(x, y) > 0))
    
    Eq << ~Eq[0]
    
    Eq << algebra.forall.exists.imply.exists_et.apply(Eq[1], Eq[-1])

if __name__ == '__main__':
    prove()

