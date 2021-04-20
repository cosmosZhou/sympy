from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, *limits, simplify=True):
    lhs, rhs = axiom.is_Equal(given)
    lhs, rhs = UNION(lhs.set, *limits), UNION(rhs.set, *limits)
    if simplify:
        lhs, rhs = lhs.simplify(), rhs.simplify() 
        
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(shape=(), etype=dtype.integer)
    g = Function.g(shape=(), etype=dtype.integer)
    
    Eq << apply(Equal(f(i), g(i)), (i, 0, n))
    
    Eq << Eq[0].forall((i,))
    
    Eq << sets.forall_eq.imply.eq.set_comprehension.apply(Eq[-1])


if __name__ == '__main__':
    prove()

