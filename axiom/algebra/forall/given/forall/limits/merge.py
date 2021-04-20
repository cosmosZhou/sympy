from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra
from axiom.algebra.forall.imply.forall.limits.merge import merge


@apply
def apply(given):
    return merge(given)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    x = Symbol.x(real=True, shape=(oo,))
    f = Function.f(real=True)

    Eq << apply(ForAll[x[:n]:CartesianSpace(Interval(a, b), n), x[n]:Interval(a, b)](f(x[:n + 1]) > 0))
    
    Eq << algebra.forall.imply.forall.limits.split.apply(Eq[1], index=n)
    

if __name__ == '__main__':
    prove()

