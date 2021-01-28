from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets
from sympy.sets.sets import image_set
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply(imply=True)
def apply(self):
    function, *limits = axiom.is_Sum(self)
    n, a, b = axiom.limit_is_odd(limits)
    return Equality(self, Sum[n:a // 2:b // 2](function._subs(n, 2 * n + 1)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)

    f = Symbol.f(shape=(oo,), real=True)
    
    a = Symbol.a(integer=True)
    
    b = Symbol.b(integer=True)
    
    Eq << apply(Sum[n:(-1) ** n < 0:Interval(a, b, integer=True)](f[n]))

    Eq << Eq[-1].this.lhs.apply(algebre.imply.equal.sum.bool)
    
    S = Symbol.S(definition=image_set(2 * n + 1, n, Eq[-1].rhs.limits_condition))
    
    Eq << S.this.definition
    
    Eq << algebre.imply.equal.sum.bool.apply(Sum[n:S](f[n]))
    
    Eq << Eq[-1].this.lhs.limits[0][1].definition
    
    Eq << Eq[1].subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.function.args[1].arg.rhs.definition
    
    Eq << Eq[-1].this.lhs.function.args[1].arg.apply(sets.imply.equivalent.et.astype.contains.where.is_odd, split=False)


if __name__ == '__main__':
    prove(__file__)

