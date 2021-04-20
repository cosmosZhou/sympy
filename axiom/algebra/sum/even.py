from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    function, *limits = axiom.is_Sum(self)
    n, a, b = axiom.limit_is_even(limits)
    return Equal(self, Sum[n:(a + 1) // 2:(b + 1) // 2](function._subs(n, 2 * n)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)

    f = Symbol.f(shape=(oo,), real=True)
    
    a = Symbol.a(integer=True)
    
    b = Symbol.b(integer=True)
    
    Eq << apply(Sum[n:Equal(n % 2, 0):Interval(a, b, integer=True)](f[n]))
    
    Eq << Eq[-1].this.lhs.apply(algebra.sum.bool)
    
    S = Symbol.S(imageset(n, 2 * n, Eq[-1].rhs.limits_cond))
    
    Eq << S.this.definition
    
    Eq << algebra.sum.bool.apply(Sum[n:S](f[n]))
    
    Eq << Eq[-1].this.lhs.limits[0][1].definition
    
    Eq << Eq[1].subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.function.args[1].arg.rhs.definition
    
    Eq << Eq[-1].this.lhs.function.args[1].arg.apply(sets.et.to.contains.split.is_even)


if __name__ == '__main__':
    prove()

