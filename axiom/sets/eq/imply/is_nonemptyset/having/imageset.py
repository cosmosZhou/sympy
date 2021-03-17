from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
import axiom
# given : A \ B = A

# => A & B = EmptySet


@apply
def apply(given):
    imageSet, s = axiom.is_Equal(given)
    x, fx, cond = axiom.is_ImageSet(imageSet)
    fy = axiom.is_FiniteSet(s)
    
    z = Wild('z', **x.type.dict)
    fx_ = fx._subs(x, z)
    values = fy.match(fx_)
    y = values[z]
    
    return Unequal(conditionset(y, cond._subs(x, y)), e.emptySet)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    
    Eq << apply(Equality(imageset(x, f(x), g(x) > 0), {f(y)}))
    
    A = Symbol.A(Eq[1].lhs)
    
    Eq.A_definition = A.this.definition
    
    Eq << imageset(x, f(x), A).this.subs(Eq.A_definition)
    
    Eq << Eq[-1].this.rhs.limits_subs(y, x)
    
    Eq << algebre.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[0])
    
    Eq << Eq[1].subs(Eq.A_definition.reversed)
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-3].subs(Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

