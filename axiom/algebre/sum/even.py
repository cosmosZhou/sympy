from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    function, *limits = axiom.is_Sum(self)
    n, a, b = axiom.limit_is_even(limits)
    return Equality(self, Sum[n:(a + 1) // 2:(b + 1) // 2](function._subs(n, 2 * n)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)

    f = Symbol.f(shape=(oo,), real=True)
    
    a = Symbol.a(integer=True)
    
    b = Symbol.b(integer=True)
    
    Eq << apply(Sum[n:(-1) ** n > 0:Interval(a, b, integer=True)](f[n]))
    
    Eq << Eq[-1].this.lhs.apply(algebre.sum.bool)
    
    S = Symbol.S(imageset(n, 2 * n, Eq[-1].rhs.limits_condition))
    
    Eq << S.this.definition
    
    Eq << algebre.sum.bool.apply(Sum[n:S](f[n]))
    
    Eq << Eq[-1].this.lhs.limits[0][1].definition
    
    Eq << Eq[1].subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.function.args[1].arg.rhs.definition
    
    Eq << Eq[-1].this.lhs.function.args[1].arg.apply(sets.et.astype.contains.where.is_even, split=False)


if __name__ == '__main__':
    prove(__file__)

