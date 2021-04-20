from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebra



# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply
def apply(*given):
    is_odd, contains_n = given     
    n = axiom.is_odd(is_odd)
    n_, ab = axiom.is_Contains(contains_n)
    
    assert n == n_
    axiom.is_integer_Interval(ab)
    a, b = ab.min(), ab.max()
    
    return Contains(n, imageset(n, 2 * n + 1, Interval(a // 2, (b - 1) // 2, integer=True)))


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    n = Symbol.n(integer=True)

    Eq << apply(Equal(n % 2, 1), Contains(n, Interval(a, b, integer=True)))
    
    Eq << algebra.is_odd.imply.exists.apply(Eq[0])
    
    Eq << algebra.cond.exists.imply.exists_et.apply(Eq[1], Eq[-1], simplify=None)
    
    Eq << Eq[-1].this.function.apply(algebra.et.imply.et.subs)
    
    Eq << Eq[-1].this.find(Contains).apply(sets.contains.imply.contains.interval.sub, 1, simplify=None)    
    
    Eq << Eq[-1].this.find(Contains).apply(sets.contains.imply.contains.interval.div.integer, 2, simplify=None)
    
    Eq << Eq[-1].this.find(Equal) - 1
    
    Eq << Eq[-1].this.find(Equal) / 2
    
    Eq << Eq[-1].this.rhs.args[0].apply(algebra.ceiling.to.floor)
    
    S = Symbol.S(conditionset(n, Eq[-1]))
    Eq << S.this.definition
    
    Eq << Eq[-1].this.rhs.limits_subs(n, 2 * n + 1)
    
    Eq << Contains(n, S, plausible=True)
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-1].subs(Eq[-2])

    
if __name__ == '__main__':
    prove()

