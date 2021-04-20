from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(*given, reverse=False): 
    eq, f_eq = given
    f_eq, *limits_e = axiom.is_Exists(f_eq)    
    eq, *limits_f = axiom.forall_eq(eq)
    
    assert limits_f == limits_e
    lhs, rhs = eq.args
    if reverse:
        lhs, rhs = rhs, lhs
            
    return Exists(f_eq._subs(lhs, rhs), *limits_f)


@prove
def prove(Eq):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    
    a = Symbol.a(real=True, shape=(m, n))
    b = Symbol.b(real=True, shape=(m, n))
    c = Symbol.c(real=True, shape=(m, n))
    
    f = Function.f(real=True)
    
    C = Symbol.C(etype=dtype.real * (m, n))    
    S = Symbol.S(etype=dtype.real * (m, n))
    
    Eq << apply(ForAll[c:C](Equal(a, f(c))), Exists[c:C](Contains(a * b + c, S)))
    
    Eq << algebra.forall.exists.imply.exists_et.apply(Eq[0], Eq[1])
    
    Eq << Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs)

    
if __name__ == '__main__':
    prove()
