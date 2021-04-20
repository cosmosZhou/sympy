from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(*given):    
    eq, f_eq = given
    lhs, rhs = axiom.is_Equal(eq)
    
    args = axiom.is_Mul(lhs)
    args = [arg for arg in args if not arg.is_OneMatrix]
    lhs_without_ones = lhs.func(*args)
        
    assert f_eq._subs(lhs_without_ones, lhs) == f_eq
    
    return f_eq._subs(lhs_without_ones, rhs)


@prove
def prove(Eq):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    
    a = Symbol.a(real=True, shape=(n,))
    b = Symbol.b(real=True, shape=(m, n))
    c = Symbol.c(real=True, shape=(m, n))
    
    S = Symbol.S(etype=dtype.real * (m, n))
    Eq << apply(Equal(a * OneMatrix(m, n), c), Contains(a * b, S))
    
    a = Symbol.a(a * OneMatrix(m, n))
    
    Eq << a.this.definition
    
    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[0], Eq[-1])
    
    Eq << Eq[-2] * b
    
    Eq << Eq[1].subs(Eq[-1].reversed)
    
    Eq << Eq[-1].subs(Eq[-3].reversed)
        
    
if __name__ == '__main__':
    prove()
