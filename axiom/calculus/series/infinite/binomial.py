from sympy import *
from axiom.utility import prove, apply
from axiom import algebra


@apply
def apply(r, x=None, n=None):
    assert r.is_real
    if x is None:
        x = Symbol.x(real=True)
        
    if n is None:
        n = Symbol.n(integer=True)
        
    return Equal((1 + x) ** r, Sum[n:0:oo](binomial(r, n) * x ** n))


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    r = Symbol.r(real=True)    
    n = Symbol.n(integer=True)
    Eq << apply(r, x=x, n=n)


if __name__ == '__main__':
    prove()

