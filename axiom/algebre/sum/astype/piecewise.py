from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    function, *limits = axiom.is_Sum(self)    
    variables = self.variables

    for expr, cond in axiom.is_Piecewise(function):
        assert not cond.has(*variables)
    
    ecs = [(self.func(expr, *limits).simplify(), cond) for expr, cond in axiom.is_Piecewise(function)]
    
    return Equality(self, Piecewise(*ecs))


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    C = Symbol.C(etype=dtype.integer, given=True)
    D = Symbol.D(etype=dtype.integer, given=True)
    
    f = Function.f(real=True)
    h = Function.h(real=True)
    
    Eq << apply(Sum[j:D, i:C](Piecewise((f(i, j), Contains(x, A) & Contains(y, B)), (h(i, j), True))))

    Eq << algebre.eq.given.ou.apply(Eq[0])
    
    Eq << Eq[-1].this.args[1].apply(algebre.et.given.et.subs, index=Slice[:2], split=False)
    
    Eq << Eq[-1].this.args[0].apply(algebre.et.given.et.subs, index=0, split=False, invert=True)
    
    Eq << Eq[-1].astype(And)


if __name__ == '__main__':
    prove(__file__)

