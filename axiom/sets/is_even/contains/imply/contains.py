from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebra


# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply
def apply(*given):
    is_even, contains_n = given     
    n = axiom.is_even(is_even)
    n_, ab = axiom.is_Contains(contains_n)
    
    assert n == n_
    a, b = axiom.is_Interval(ab, integer=True)
    b -= 1
    
    return Contains(n, imageset(n, 2 * n, Interval((a + 1) // 2, b // 2, integer=True)))


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    n = Symbol.n(integer=True)

    Eq << apply(Equal(n % 2, 0), Contains(n, Interval(a, b, integer=True)))
    
    Eq << algebra.is_even.imply.exists.apply(Eq[0])
    
    Eq << Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs, Eq[1])
    
    Eq << Eq[-1].this.function.apply(sets.contains.imply.contains.interval.div.integer, 2, simplify=None)
    
    Eq << Eq[-3].this.function.apply(algebra.eq.imply.eq.divide, 2, simplify=None)
    
    Eq << Eq[-1].this.function.apply(algebra.eq.imply.eq.reversed, simplify=None)
    
    Eq <<= Eq[-3] & Eq[-1]
    
    Eq << Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs)    
    
    Eq << Eq[-1].this.rhs.args[0].apply(algebra.ceiling.to.floor)
    
    S = Symbol.S(conditionset(n, Eq[-1]))
    Eq << S.this.definition
    
    Eq << Eq[-1].this.rhs.limits_subs(n, 2 * n)
    
    Eq << Contains(n, S, plausible=True)
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-1].subs(Eq[-2])

    
if __name__ == '__main__':
    prove()

