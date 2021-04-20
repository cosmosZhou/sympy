from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    eq, *limits = axiom.forall_eq(given)
    lhs, rhs = eq.args
    
    return Equal(ArgMax(lhs, *limits).simplify(), ArgMax(rhs, *limits).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(ForAll[x:a:b](Equal(f(x), g(x))))
    
    x_ = Symbol.x(domain=Interval(a, b))
    
    Eq << algebra.forall.imply.cond.subs.apply(Eq[0], x, x_)
    
    Eq << Eq[1].this.lhs.limits_subs(x, x_)
    
    Eq << Eq[-1].this.rhs.limits_subs(x, x_)
    
    Eq << Eq[-1].this.lhs.subs(Eq[2])
    

if __name__ == '__main__':
    prove()

