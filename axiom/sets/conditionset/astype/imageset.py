from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
import axiom


@apply
def apply(self):
    axiom.is_ConditionSet(self)
    variable, expr, base_set = self.base_set.image_set()
    if base_set.is_boolean:
        condition = base_set & self.condition._subs(self.variable, expr)
    else:
        condition = Contains(variable, base_set).simplify() & self.condition._subs(self.variable, expr)
    return Equal(self, imageset(variable, expr, conditionset(variable, condition)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    
    x = Symbol.x(complex=True, shape=(n,))
    y = Symbol.y(complex=True, shape=(m,))
    
    A = Symbol.A(etype=dtype.complex * n)
    f = Function.f(complex=True, shape=(m,))
    
    g = Function.g(shape=(), real=True)
    
    s = Symbol.s(imageset(x, f(x), A))

    Eq << apply(conditionset(y, g(y) > 0, s))
    
    Eq << Eq[1].this.lhs.limits[0][2].definition
    
    B = Symbol.B(Eq[-1].lhs)
    B_quote = Symbol("B'", Eq[-1].rhs)
    
    Eq << B.this.definition
    
    Eq << B_quote.this.definition

    Eq.sufficient = Sufficient(Contains(y, B), Contains(y, B_quote), plausible=True)
    
    Eq << Eq.sufficient.this.rhs.rhs.definition

    Eq << Eq[-1].this.rhs.apply(sets.contains.given.exists_equal.where.imageset)
    
    Eq << Eq[-1].this.lhs.rhs.definition
    
    Eq << Eq[-1].this.rhs.apply(algebre.exists.given.exists_et, depth=0)
    
    Eq << Eq[-1].this.lhs.args[1].apply(sets.contains.imply.exists_equal.where.imageset)
    
    Eq << Eq[-1].this.rhs.function.apply(algebre.et.given.et.where.equal, split=False, reverse=True)    
    
    Eq.necessary = Necessary(Contains(y, B), Contains(y, B_quote), plausible=True)
    
    Eq << Eq.necessary.this.rhs.rhs.definition
    
    Eq << Eq[-1].this.rhs.apply(sets.contains.imply.exists_equal.where.imageset)
    
    Eq << Eq[-1].this.rhs.apply(algebre.exists.imply.exists_et.single_variable, depth=0)

    Eq << Eq[-1].this.rhs.apply(algebre.et.imply.et.subs, split=False, reverse=True)
    
    Eq << Eq[-1].this.lhs.rhs.definition
    
    Eq << Eq[-1].this.lhs.args[1].apply(sets.contains.given.exists_equal.where.imageset)
    
    Eq << sets.sufficient.necessary.imply.equal.apply(Eq.sufficient, Eq.necessary)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.rhs.definition


if __name__ == '__main__':
    prove(__file__)

