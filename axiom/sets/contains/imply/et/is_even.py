from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets
from sympy.sets.sets import image_set


# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply(imply=True)
def apply(given):
    n, image_set = axiom.is_Contains(given)     
    expr, _n, cond = axiom.is_ImageSet(image_set)
    
    assert expr == 2 * n
    
    a, b = axiom.is_Interval(cond, integer=True,end=None)
    b -= 1
    
    assert n == _n
    
    a = axiom.is_Floor(a)
    a = 2 * a - 1
    
    b = axiom.is_Floor(b)
    b = 2 * b
    
    return And((-1) ** n > 0, Contains(n, Interval(a, b, integer=True)))


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(Contains(n, image_set(2 * n, n, Interval((a + 1) // 2, b // 2, integer=True))))

    
if __name__ == '__main__':
    prove(__file__)

