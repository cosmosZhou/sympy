from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebre


# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply
def apply(given):
    n, image_set = axiom.is_Contains(given)     
    _n, expr, cond = axiom.is_ImageSet(image_set)
    
    assert expr == 2 * n
    
    a, b = axiom.is_Interval(cond, integer=True)
    b -= 1
    
    assert n == _n
    
    a = axiom.is_Floor(a)
    a = 2 * a - 1
    
    b = axiom.is_Floor(b)
    b = 2 * b
    
    return And(Equal(n % 2, 0), Contains(n, Interval(a, b, integer=True)))


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(Contains(n, imageset(n, 2 * n, Interval((a + 1) // 2, b // 2, integer=True))))
    
    S = Symbol.S(Eq[0].rhs)
    Eq << S.this.definition
    
    Eq << Eq[-1].this.rhs.limits_subs(n, n / 2)
    
    Eq << Contains(n, S, plausible=True)
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq.contains = Eq[-1].subs(Eq[-2])
    
    Eq << sets.contains.imply.contains.interval.multiply.apply(Eq.contains, 2)
    
    Eq << sets.contains.imply.et.interval.apply(Eq[-1])
    
    Eq << algebre.et.imply.cond.apply(Eq[-1])
    
    Eq << algebre.ge.ge.imply.ge.transit.apply(Eq[-1], algebre.imply.ge.floor.apply(a + 1, 2))
    
    Eq << algebre.le.le.imply.le.transit.apply(Eq[-3], algebre.imply.le.floor.apply(b, 2))
    
    Eq << sets.ge.le.imply.contains.apply(Eq[-2], Eq[-1])
    
    Eq << Subset(Eq.contains.rhs, Integers, plausible=True)
    
    Eq << sets.contains.subset.imply.contains.apply(Eq.contains, Eq[-1])
    
    Eq << sets.contains.imply.exists_eq.definition.apply(Eq[-1])
    
    Eq << Eq[-1] * 2
    
    Eq << Eq[-1] % 2
    
    Eq << algebre.et.given.cond.apply(Eq[1])
    
    
if __name__ == '__main__':
    prove(__file__)

