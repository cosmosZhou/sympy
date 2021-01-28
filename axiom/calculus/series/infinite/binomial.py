
from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy import Symbol
from axiom.discrete.combinatorics.binomial import Pascal
from sympy.concrete.summations import Sum
from sympy.core.add import Plus
from axiom import algebre
from sympy.core.numbers import oo


@apply(imply=True)
def apply(r, x=None, n=None):
    assert r.is_real
    if x is None:
        x = Symbol.x(real=True)
        
    if n is None:
        n = Symbol.n(integer=True)
        
    return Equality((1 + x) ** r, Sum[n:0:oo](binomial(r, n) * x ** n))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    r = Symbol.r(real=True)    
    n = Symbol.n(integer=True)
    Eq << apply(r, x=x, n=n)

if __name__ == '__main__':
    prove(__file__)

