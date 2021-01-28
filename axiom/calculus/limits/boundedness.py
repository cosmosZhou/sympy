from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre


@apply(imply=True)
def apply(given):
    lim, a = axiom.is_Equal(given)
    expr, n, *_ = lim.args
    assert n.is_integer
    M = Symbol.M(real=True, positive=True)
    return Exists[M](ForAll[n](abs(expr) <= M))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    x = Symbol.x(real=True, shape=(oo,), given=True)
    a = Symbol.a(real=True, given=True)
    
    Eq << apply(Equal(Limit(x[n], n, oo), a))

    Eq << algebre.equal.imply.exists.definition.limit.apply(Eq[0])
    
    ε = Eq[-1].function.function.rhs
    
    Eq << Eq[-1].this.function.function.apply(algebre.strict_less_than.imply.strict_less_than.abs.max)
    
    Eq.strict_less_than = Eq[-1].subs(ε, S.Half)
    
    N = Eq.strict_less_than.variable
    
    a_max = Eq.strict_less_than.function.function.rhs
    M = Symbol.M(definition=Max(a_max, Maximize[n:N + 1](abs(x[n]))))
    
    Eq << M.this.definition
    
    Eq << LessThan(a_max, M, plausible=True)
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq.strict_less_than.this.function.function.apply(algebre.strict_less_than.less_than.imply.strict_less_than.transit, Eq[-1])
    
    Eq.less_than = Eq[-1].this.function.function.apply(algebre.strict_less_than.imply.less_than)
    
    Eq << algebre.imply.forall_greater_than.max.apply(Maximize[n:N + 1](abs(x[n])))
    
    Eq << LessThan(Maximize[n:N + 1](abs(x[n])), M, plausible=True)
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-2].this.function.apply(algebre.greater_than.less_than.imply.less_than.transit, Eq[-1])
    
    Eq << algebre.exists_forall.forall.imply.exists_forall.apply(Eq.less_than, Eq[-1])
    
    Eq << Eq[-1].this.function.simplify()
    
    Eq << algebre.exists.given.exists.subs.apply(Eq[1], Eq[1].variable, M)
    

if __name__ == '__main__':
    prove(__file__)

