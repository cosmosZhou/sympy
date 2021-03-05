from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
import axiom


@apply
def apply(self):
    x, expr, et = axiom.is_ImageSet(self)
    if et.is_ConditionSet:
        et = et.condition & Contains(x, et.base_set)
    eqs = axiom.is_And(et)
    for eq in eqs:
        if eq.is_Equal: 
            return Equal(self, imageset(x, expr._subs(*eq.args), et).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    
    x = Symbol.x(complex=True, shape=(n,))
    f = Function.f(complex=True, shape=(m,))        
    g = Function.g(complex=True, shape=(m,))
    
    h = Function.h(shape=(), real=True)
    
    Eq << apply(imageset(x, f(x), Equal(f(x), g(x)) & (h(x) > 0)))
    
    Eq << Eq[0].this.lhs.apply(sets.union.bool)
    
    Eq << Eq[-1].this.lhs.function.apply(algebre.piecewise.subs)

if __name__ == '__main__':
    prove(__file__)

