from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_LessEqual(given)
    
    return LessEqual(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(LessEqual(f(i), g(i)), (i, 0, n))
    
    Eq << Eq[0].apply(algebra.cond.imply.forall.restrict, (i, 0, n))
    
    Eq << algebra.forall_le.imply.le.sum.apply(Eq[-1])


if __name__ == '__main__':
    prove()

