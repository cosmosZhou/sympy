from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre, calculus


@apply
def apply(given):
    lim, a = axiom.is_Equal(given)
    expr, (n, *_) = lim.args
    assert n.is_integer
    M = Symbol.M(real=True, positive=True)
    return Exists[M](ForAll[n](abs(expr) <= M))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    x = Symbol.x(real=True, shape=(oo,), given=True)
    a = Symbol.a(real=True, given=True)
    
    Eq << apply(Equal(Limit[n:oo](x[n]), a))

    Eq << calculus.eq.imply.exists.definition.limit.apply(Eq[0])
    
    ε = Eq[-1].function.function.rhs
    
    Eq << Eq[-1].this.function.function.apply(algebre.lt.imply.lt.abs.max)
    
    Eq.lt = Eq[-1].subs(ε, S.Half)
    
    N = Eq.lt.variable
    
    a_max = Eq.lt.function.function.rhs
    M = Symbol.M(Max(a_max, Maximize[n:N + 1](abs(x[n]))))
    
    Eq << M.this.definition
    
    Eq << LessThan(a_max, M, plausible=True)
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq.lt.this.function.function.apply(algebre.lt.le.imply.lt.transit, Eq[-1])
    
    Eq.less_than = Eq[-1].this.function.function.apply(algebre.lt.imply.le.relaxed)
    
    Eq << algebre.imply.forall_ge.max.apply(Maximize[n:N + 1](abs(x[n])))
    
    Eq << LessThan(Maximize[n:N + 1](abs(x[n])), M, plausible=True)
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-2].this.function.apply(algebre.ge.le.imply.le.transit, Eq[-1])
    
    Eq << algebre.exists_forall.forall.imply.exists_forall.apply(Eq.less_than, Eq[-1])
    
    Eq << Eq[-1].this.function.simplify()
    
    Eq << algebre.exists.given.exists.subs.apply(Eq[1], Eq[1].variable, M)
    

if __name__ == '__main__':
    prove(__file__)

