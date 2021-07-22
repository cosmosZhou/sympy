from util import *


@apply
def apply(eq, f_eq, swap=False, reverse=False):
    if swap:
        f_eq, eq = eq, f_eq
        
    lhs, rhs = eq.of(Equal)
    assert f_eq.is_Equal
    
    if reverse:
        lhs, rhs = rhs, lhs    
    
    return f_eq._subs(lhs, rhs)


@prove
def prove(Eq):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True, shape=(m, n))
    b = Symbol.b(real=True, shape=(m, n))
    c = Symbol.c(real=True, shape=(m, n))
    d = Symbol.d(real=True, shape=(m, n))
    Eq << apply(Equal(a, 2 * c), Equal(a * b, d))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
from . import rhs
from . import lhs
