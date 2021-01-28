from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply(imply=True)
def apply(given):
    eq, *limits = axiom.forall_equal(given)
    lhs, rhs = eq.args
    
    return Equality(MIN(lhs, *limits).simplify(), MIN(rhs, *limits).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(ForAll[x:a:b](Equality(f(x), g(x))))
    
    x_ = Symbol.x(domain=Interval(a, b))
    
    Eq << Eq[0].subs(x, x_)
    
    Eq << Eq[1].this.lhs.limits_subs(x, x_)
    
    Eq << Eq[-1].this.rhs.limits_subs(x, x_)
    
    Eq << Eq[-1].this.lhs.subs(Eq[2])
    

if __name__ == '__main__':
    prove(__file__)

