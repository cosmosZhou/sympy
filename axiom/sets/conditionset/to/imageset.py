from util import *


@apply
def apply(self):
    assert self.is_ConditionSet
    variable, expr, base_set = self.base_set.image_set()
    if base_set.is_boolean:
        condition = base_set & self.condition._subs(self.variable, expr)
    else:
        condition = Element(variable, base_set).simplify() & self.condition._subs(self.variable, expr)
    return Equal(self, imageset(variable, expr, conditionset(variable, condition)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n, m = Symbol(integer=True, positive=True)

    x = Symbol(complex=True, shape=(n,))
    y = Symbol(complex=True, shape=(m,))

    A = Symbol(etype=dtype.complex * n)
    f = Function(complex=True, shape=(m,))

    g = Function(shape=(), real=True)

    s = Symbol(imageset(x, f(x), A))

    Eq << apply(conditionset(y, g(y) > 0, s))

    Eq << Eq[1].this.lhs.limits[0][2].definition

    B = Symbol(Eq[-1].lhs)
    B_quote = Symbol(Eq[-1].rhs)

    Eq << B.this.definition

    Eq << B_quote.this.definition

    Eq.suffice = Suffice(Element(y, B), Element(y, B_quote), plausible=True)

    Eq << Eq.suffice.this.rhs.rhs.definition

    Eq << Eq[-1].this.rhs.apply(sets.el.given.any_eq.split.imageset)

    Eq << Eq[-1].this.lhs.rhs.definition

    Eq << Eq[-1].this.rhs.apply(algebra.any.given.any_et.limits.unleash)

    Eq << Eq[-1].this.lhs.args[1].apply(sets.el.imply.any_eq.split.imageset)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.et.given.et.split.eq, reverse=True)

    Eq.necessary = Necessary(Element(y, B), Element(y, B_quote), plausible=True)

    Eq << Eq.necessary.this.rhs.rhs.definition

    Eq << Eq[-1].this.rhs.apply(sets.el.imply.any_eq.split.imageset)

    Eq << Eq[-1].this.rhs.apply(algebra.any.imply.any_et.limits.single_variable)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.et.imply.et.subs, reverse=True)

    Eq << Eq[-1].this.lhs.rhs.definition

    Eq << Eq[-1].this.lhs.args[1].apply(sets.el.given.any_eq.split.imageset)

    Eq << sets.suffice.necessary.imply.eq.apply(Eq.suffice, Eq.necessary)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition


if __name__ == '__main__':
    run()

