from util import *


@apply
def apply(self):
    fx, (x, s) = self.of(Cap)
    return Equal(self, fx.as_multiple_terms(x, s, cls=Cap))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(etype=dtype.real)
    g = Function.g(etype=dtype.real)

    Eq << apply(Cap[x:B](Piecewise((f(x, y), Contains(x, A)), (g(x, y), True))))

    Eq << sets.eq.given.suffice.apply(Eq[0], wrt='y')

    Eq <<= Eq[-2].this.lhs.apply(sets.contains.imply.all_contains.st.cap), \
    Eq[-1].this.rhs.apply(sets.contains.given.all_contains.st.cap)

    Eq <<= Eq[-2].this.lhs.function.apply(sets.contains.imply.ou.st.piecewise), \
    Eq[-1].this.rhs.function.apply(sets.contains.given.ou.st.piecewise)

    Eq <<= Eq[-2].this.rhs.apply(sets.contains.given.contains.split.intersection, simplify=None), \
    Eq[-1].this.lhs.apply(sets.contains.imply.contains.split.intersection, simplify=None)

    Eq <<= Eq[-2].this.rhs.find(Contains).apply(sets.contains.given.all_contains.st.cap), \
    Eq[-1].this.lhs.find(Contains).apply(sets.contains.imply.all_contains.st.cap)

    Eq <<= Eq[-2].this.rhs.find(Contains).apply(sets.contains.given.all_contains.st.cap), \
    Eq[-1].this.lhs.find(Contains).apply(sets.contains.imply.all_contains.st.cap)

    Eq <<= Eq[-2].this.lhs.split(A), Eq[-1].this.rhs.split(A)

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.all.to.suffice), Eq[-1].this.rhs.args[0].apply(algebra.all.to.suffice)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.apply(sets.contains.to.et.st.intersection, index=0, simplify=False), \
    Eq[-1].this.rhs.args[0].lhs.apply(sets.contains.to.et.st.intersection, index=0, simplify=False)

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.suffice.subs.bool, index=0, invert=True), \
    Eq[-1].this.rhs.args[0].apply(algebra.suffice.subs.bool, index=0, invert=True)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.args[1].apply(sets.contains.to.et.st.intersection), \
    Eq[-1].this.rhs.args[0].lhs.args[1].apply(sets.contains.to.et.st.intersection)

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.suffice.to.all, wrt=x), \
    Eq[-1].this.rhs.args[0].apply(algebra.suffice.to.all, wrt=x)

    Eq <<= Eq[-2].this.lhs.args[1].apply(algebra.all.to.suffice), Eq[-1].this.rhs.apply(algebra.all.to.suffice)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.apply(sets.contains.to.et.st.complement), \
    Eq[-1].this.rhs.lhs.apply(sets.contains.to.et.st.complement)

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.suffice.subs.bool, index=1, invert=True), \
    Eq[-1].this.rhs.apply(algebra.suffice.subs.bool, index=1, invert=True)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.simplify(), Eq[-1].this.rhs.lhs.simplify()

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.suffice.to.all, wrt=x), \
    Eq[-1].this.rhs.apply(algebra.suffice.to.all, wrt=x)


if __name__ == '__main__':
    run()

