from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(*given, reverse=False): 
    eq, f_eq = given
    assert not f_eq.is_ConditionalBoolean
    eq, *limits = axiom.forall_eq(eq)
    lhs, rhs = eq.args
    if reverse:
        lhs, rhs = rhs, lhs    
    return ForAll(f_eq._subs(lhs, rhs), *limits)


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
    
    Eq << apply(ForAll[c:C](Equal(a, f(c))), Contains(a * b + c, S))
    
    Eq << algebra.cond.forall.imply.forall_et.apply(Eq[1], Eq[0])
    
    Eq << Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs)

    
if __name__ == '__main__':
    prove()
