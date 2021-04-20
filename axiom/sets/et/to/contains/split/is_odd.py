from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebra


# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply(given=None)
def apply(given):
    is_odd, contains_n = axiom.is_And(given)     
    n = axiom.is_odd(is_odd)
    n_, ab = axiom.is_Contains(contains_n)
    
    assert n == n_
    axiom.is_integer_Interval(ab)
    a, b = ab.min(), ab.max()
    
    return Equivalent(given, Contains(n, imageset(n, 2 * n + 1, Interval(a // 2, (b - 1) // 2, integer=True))))


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    n = Symbol.n(integer=True)

    Eq << apply(Equal(n % 2, 1) & Contains(n, Interval(a, b, integer=True)))

    Eq << algebra.equivalent.given.cond.apply(Eq[0])
        
    Eq << Eq[-2].this.lhs.apply(sets.is_odd.contains.imply.contains)
    
    Eq << Eq[-1].this.rhs.apply(sets.contains.imply.et.is_odd)
    
    
if __name__ == '__main__':
    prove()

