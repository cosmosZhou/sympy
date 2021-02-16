from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebre


@apply(imply=True)
def apply(*given):    
    eq, f_eq = given
    lhs, rhs = axiom.is_Equal(eq)
    
    return f_eq._subs(lhs, rhs)


@prove
def prove(Eq):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    
    a = Symbol.a(real=True, shape=(m, n))
    b = Symbol.b(real=True, shape=(m, n))
    c = Symbol.c(real=True, shape=(m, n))
    
    S = Symbol.S(etype=dtype.real * (m, n))
    Eq << apply(Equality(a, 2 * c), Contains(a * b, S))
    
    Eq << Eq[1].subs(Eq[0])
    
if __name__ == '__main__':
    prove(__file__)
