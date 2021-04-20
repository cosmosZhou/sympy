from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebra



# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply(given=None)
def apply(given):
    is_even, contains_n = axiom.is_And(given)     
    n = axiom.is_even(is_even)
    n_, ab = axiom.is_Contains(contains_n)
    
    assert n == n_
    a, b = axiom.is_Interval(ab, integer=True)
    b -= 1
    
    return Equivalent(given, Contains(n, imageset(n, 2 * n, Interval((a + 1) // 2, b // 2, integer=True))))


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    n = Symbol.n(integer=True)

    Eq << apply(Equal(n % 2, 0) & Contains(n, Interval(a, b, integer=True)))
    
    Eq << algebra.equivalent.given.cond.apply(Eq[0])    
    
    Eq << Eq[-2].this.lhs.apply(sets.is_even.contains.imply.contains)
    
    Eq << Eq[-1].this.rhs.apply(sets.contains.imply.et.is_even)

    
if __name__ == '__main__':
    prove()

