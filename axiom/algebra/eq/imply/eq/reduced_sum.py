from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra, sets


@apply
def apply(given, *, simplify=True): 
    lhs, rhs = axiom.is_Equal(given)
    
    lhs, rhs = ReducedSum(lhs), ReducedSum(rhs)
    if simplify:
        lhs = lhs.simplify()
        rhs = rhs.simplify()
    
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    assert i.is_integer
    f = Function.f(shape=(), complex=True)
    g = Function.g(shape=(), complex=True)
    
    Eq << apply(Equal(f(i), g(i)))
    
    Eq << Eq[1].subs(Eq[0])
    
    
if __name__ == '__main__':
    prove()

