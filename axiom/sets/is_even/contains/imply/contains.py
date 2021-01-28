from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets
from sympy.sets.sets import image_set


# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply(imply=True)
def apply(*given):
    is_even, contains_n = given     
    n = axiom.is_even(is_even)
    n_, ab = axiom.is_Contains(contains_n)
    
    assert n == n_
    a, b = axiom.is_Interval(ab, integer=True, end=None)
    b -= 1
    
    return Contains(n, image_set(2 * n, n, Interval((a + 1) // 2, b // 2, integer=True)))


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(Equal(n % 2, 0), Contains(n, Interval(a, b, integer=True)))

    
if __name__ == '__main__':
    prove(__file__)

