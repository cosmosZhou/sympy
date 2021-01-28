from sympy import *
from axiom.utility import prove, apply

import axiom
from axiom import sets, algebre
# given : A & B = A | B => A = B


@apply(imply=True)
def apply(given):
    x_y, a = axiom.is_Equal(given)
    x, y = axiom.is_FiniteSet(x_y, 2)
    a0, a1 = axiom.is_FiniteSet(a, 2)
    
    a, zero = axiom.is_Indexed(a0)
    a, one = axiom.is_Indexed(a1)

    assert zero.is_zero
    assert one.is_One
    
    return Equality(Matrix([x, y]), Matrix([a[1 - KroneckerDelta(a0, x)], a[KroneckerDelta(a0, x)]]))


@prove
def prove(Eq):
    x = Symbol.x(etype=dtype.complex, given=True)
    y = Symbol.y(etype=dtype.complex, given=True)
    a = Symbol.a(etype=dtype.complex, shape=(oo,), given=True)
    
    Eq << apply(Equality({x, y}, {a[0], a[1]}))
    
    Eq << Eq[1].split()
    
    Eq << Contains(x, {x, y}, plausible=True)
    
    Eq.x_contains = Eq[-1].subs(Eq[0])
    
    Eq << sets.contains.imply.ou.where.finiteset.two.apply(Eq.x_contains, simplify=False)

    Eq << Eq[2].bisect(Equality(x, a[0])).split()
    
    Eq <<= ~Eq[-2], ~Eq[-1]
    
    Eq <<= Eq[-2].apply(algebre.unequal.condition.imply.et), Eq[-1].apply(algebre.equal.condition.imply.et)
    
    Eq << Eq[-1].apply(sets.unequal.unequal.imply.notcontains, simplify=False)
    
    Eq <<= Eq.x_contains & Eq[-1]
    
    Eq << Eq[3].bisect(Equality(x, a[0])).split()
    
    Eq <<= ~Eq[-2], ~Eq[-1]
    
    Eq.a00, Eq.a01 = Eq[-2].apply(algebre.unequal.condition.imply.et), Eq[-1].apply(algebre.equal.condition.imply.et)
    
    Eq << Eq.a00.apply(sets.unequal.unequal.imply.notcontains, simplify=False)    
    
    Eq << Contains(a[0], {a[0], a[1]}, plausible=True)

    Eq << Eq[-1].subs(Eq[0].reversed)
    
    Eq <<= Eq[-1] & Eq[-3]

    Eq << Contains(y, {x, y}, plausible=True)
    
    Eq.y_contains = Eq[-1].subs(Eq[0])
    
    Eq << sets.contains.imply.ou.where.finiteset.two.apply(Eq.y_contains, simplify=False)
    
    Eq <<= Eq[-1] & Eq.a01
    
    Eq << Contains(a[1], {a[0], a[1]}, plausible=True)
    
    Eq << Eq[-1].subs(Eq[0].reversed)
    
    Eq << sets.contains.imply.ou.where.finiteset.two.apply(Eq[-1], simplify=False)
    
    Eq <<= Eq[-1] & Eq[-4]
    
    Eq <<= Sufficient(And(*Eq[-1].args[:2]), And(*Eq[-1].args[:2]), plausible=True), Sufficient(And(*Eq[-1].args[2:]), And(*Eq[-1].args[2:]), plausible=True)

    Eq <<= Eq[-2].this.rhs.apply(algebre.equal.equal.imply.equal.transit), Eq[-1].this.rhs.apply(algebre.equal.unequal.imply.unequal.transit)
    
    Eq << algebre.sufficient.sufficient.imply.sufficient.et.apply(Eq[-2], Eq[-1])
    
    Eq << ~Eq[-1]

    
if __name__ == '__main__':
    prove(__file__)

