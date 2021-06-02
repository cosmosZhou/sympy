
from util import *

import axiom


@apply
def apply(*given):    
    eq, f_eq = given
    if not eq.is_Equal:
        eq, f_eq = f_eq, eq    
    lhs, rhs = eq.of(Equal)
    _lhs, _rhs = f_eq.of(Unequal)
    return Unequal(_lhs._subs(lhs, rhs), _rhs._subs(lhs, rhs))




@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    f = Function.f(nargs=(n,), real=True, shape=(m,))
    g = Function.g(nargs=(n,), real=True, shape=(m,))
    
    a = Symbol.a(real=True, shape=(n,))
    b = Symbol.b(real=True, shape=(n,))
    Eq << apply(Equal(a, b), Unequal(f(a), g(a)))
    
    Eq << Eq[1].subs(Eq[0])
        
    
if __name__ == '__main__':
    run()
