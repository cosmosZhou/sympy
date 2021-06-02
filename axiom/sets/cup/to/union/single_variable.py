from util import *


@apply
def apply(self):
    import axiom
    fx, *limits = self.of(Cup)
    return Equal(self, fx.as_multiple_terms(*axiom.limit_is_set(limits), cls=Cup))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(etype=dtype.real)
    g = Function.g(etype=dtype.real)

    Eq << apply(Cup[x:B](Piecewise((f(x, y), Contains(x, A)), (g(x, y), True))))

    Eq << sets.eq.given.suffice.apply(Eq[0], wrt='y')

    Eq <<= Eq[-2].this.lhs.apply(sets.contains.imply.any_contains.st.cup), \
    Eq[-1].this.rhs.apply(sets.contains.given.any_contains.st.cup)

    Eq <<= Eq[-2].this.lhs.function.apply(sets.contains.imply.ou.st.piecewise), \
    Eq[-1].this.rhs.function.apply(sets.contains.given.ou.st.piecewise)

    Eq <<= Eq[-2].this.lhs.apply(algebra.any_ou.imply.ou.any), \
    Eq[-1].this.rhs.apply(algebra.any_ou.given.ou.any)

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.any_et.imply.any.limits_absorb, index=0), \
    Eq[-1].this.rhs.args[0].apply(algebra.any_et.given.any.limits_absorb, index=0)

    Eq <<= Eq[-2].this.lhs.args[1].apply(algebra.any_et.imply.any.limits_absorb, index=0), \
    Eq[-1].this.rhs.args[1].apply(algebra.any_et.given.any.limits_absorb, index=0)

    Eq <<= Eq[-2].this.rhs.apply(sets.contains.given.ou.split.union, simplify=None), \
    Eq[-1].this.lhs.apply(sets.contains.imply.ou.split.union, simplify=None)

    Eq <<= Eq[-2].this.rhs.find(Contains).apply(sets.contains.given.any_contains.st.cup), \
    Eq[-1].this.lhs.find(Contains).apply(sets.contains.imply.any_contains.st.cup)

    Eq << Eq[-2].this.rhs.find(Contains).apply(sets.contains.given.any_contains.st.cup)

    Eq << Eq[-1].this.lhs.find(Contains).apply(sets.contains.imply.any_contains.st.cup)


if __name__ == '__main__':
    run()

