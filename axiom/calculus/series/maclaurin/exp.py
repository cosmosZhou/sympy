from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre


@apply
def apply(x):    
    n = x.generate_free_symbol(integer=True, free_symbol='n')
    return Equality(E ** x, Sum[n:oo](x ** n / factorial(n)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(x)

if __name__ == '__main__':
    prove(__file__)

