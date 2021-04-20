from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, *limits, simplify=True):
    lhs, rhs = axiom.is_Equal(given)
    
    lhs = Product(lhs, *limits)
    rhs = Product(rhs, *limits)
    if simplify:
        lhs = lhs.simplify()
        rhs = rhs.simplify()
        
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(shape=(), complex=True)
    g = Function.g(shape=(), complex=True)
    
    Eq << apply(Equal(f(i), g(i)), (i, 0, n))
    
    Eq << Eq[0].forall((i,))
    
    Eq << algebra.forall_eq.imply.eq.product.apply(Eq[-1])


if __name__ == '__main__':
    prove()

