from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Equal(given)
    
    return Equal(LAMBDA(lhs, *limits).simplify(), LAMBDA(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    
    Eq << apply(Equal(f(i), g(i)), (i,))
    
    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], LAMBDA[i], simplify=False)


if __name__ == '__main__':
    prove()

