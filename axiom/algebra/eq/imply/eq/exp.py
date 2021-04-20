from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    lhs, rhs = axiom.is_Equal(given)    
    return Equal(exp(lhs), exp(rhs))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Equal(f(i), g(i)))
    
    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], exp)


if __name__ == '__main__':
    prove()

