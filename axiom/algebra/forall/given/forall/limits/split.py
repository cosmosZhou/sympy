from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra
from axiom.algebra.forall.imply.forall.limits.split import split


@apply
def apply(given, index=-1):
    return split(given, index)    


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    x = Symbol.x(real=True, shape=(oo,))
    f = Function.f(real=True)

    Eq << apply(ForAll[x[:n + 1]:CartesianSpace(Interval(a, b), n + 1)](f(x[:n + 1]) > 0), index=n)
    
    Eq << algebra.forall.imply.forall.limits.merge.apply(Eq[1])
    

if __name__ == '__main__':
    prove()

