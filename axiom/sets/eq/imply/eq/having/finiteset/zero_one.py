from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebre
# given : A & B = A | B => A = B


@apply
def apply(given):
    x_y, _01 = axiom.is_Equal(given)
    x, y = axiom.is_FiniteSet(x_y, 2)
    zero, one = axiom.is_FiniteSet(_01, 2)
    
    assert zero.is_zero
    assert one.is_One
    return Equality(Matrix([x, y]), Matrix([1 - KroneckerDelta(0, x), KroneckerDelta(0, x)]))


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    
    Eq << apply(Equality({x, y}, {0, 1}))
        
    Eq << algebre.eq.given.et.split.apply(Eq[1])
    
    Eq << algebre.et.given.cond.apply(Eq[-1])
    
    Eq << Contains(x, {x, y}, plausible=True)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << sets.contains.imply.eq.kronecker_delta.zero.apply(Eq[-1])
    
    Eq.x_equality = -Eq[-1] + 1
    
    Eq << Eq.x_equality.reversed
    
    Eq << sets.eq.imply.eq.having.finiteset.add.apply(Eq[0])

    Eq << Eq[-1] + Eq.x_equality
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    prove(__file__)

