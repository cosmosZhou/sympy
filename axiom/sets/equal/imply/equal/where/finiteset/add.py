from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebre
# given : A & B = A | B => A = B


@apply(imply=True)
def apply(given):
    x_y, _01 = axiom.is_Equal(given)
    x, y = axiom.is_FiniteSet(x_y, 2)
    zero, one = axiom.is_FiniteSet(_01, 2)
    
    assert zero.is_zero
    assert one.is_One
    return Equality(x + y, 1)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    
    Eq << apply(Equality({x, y}, {0, 1}))

    Eq << algebre.equal.imply.equal.sum.apply(Eq[0])
    
    Eq << Eq[-1].this.rhs.doit()    
    
    Eq << Eq[-1].this.lhs.doit()
    
    Eq << sets.equal.imply.unequal.apply(Eq[0])
    
    Eq << algebre.condition.condition.imply.condition.apply(Eq[-1], Eq[-2])

if __name__ == '__main__':
    prove(__file__)

