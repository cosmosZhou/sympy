from axiom.utility import prove, apply

from sympy import *
from axiom import sets, algebra
from axiom.algebra.exists_et.imply.exists.limits_absorb import limits_absorb


@apply
def apply(given, index):
    return limits_absorb(given, index)

@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)    
    x = Symbol.x(real=True, shape=(oo,))
    
    f = Function.f(nargs=(n,), shape=(), integer=True)
    f_quote = Function("f'", nargs=(n,), shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    h = Function.h(nargs=(n + 1,), shape=(), integer=True)

    Eq << apply(Exists[x[:n]:f(x[:n]) > 0, x[n]]((g(x[n]) > f_quote(x[:n])) & (h(x[:n + 1]) > 0)), index=0)
    
    Eq << algebra.exists.imply.exists_et.single_variable.apply(Eq[1])
    
    Eq << algebra.exists.given.exists_et.apply(Eq[0])

if __name__ == '__main__':
    prove()

