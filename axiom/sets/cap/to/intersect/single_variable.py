from util import *


@apply
def apply(self):
    fx, (x, s) = self.of(Cap)
    return Equal(self, fx.as_multiple_terms(x, s, cls=Cap))


@prove
def prove(Eq):
    from axiom import sets, algebra

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cap[x:B](Piecewise((f(x, y), Element(x, A)), (g(x, y), True))))

    Eq << sets.eq.given.et.infer.apply(Eq[0], wrt='y')

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cap.imply.all_el), \
    Eq[-1].this.rhs.apply(sets.el_cap.given.all_el)

    Eq <<= Eq[-2].this.lhs.expr.apply(sets.el_piece.imply.ou), \
    Eq[-1].this.rhs.expr.apply(sets.el_piece.given.ou)

    Eq <<= Eq[-2].this.rhs.apply(sets.el_intersect.given.et.el, simplify=None), \
    Eq[-1].this.lhs.apply(sets.el_intersect.imply.et.el, simplify=None)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(sets.el_cap.given.all_el), \
    Eq[-1].this.lhs.find(Element).apply(sets.el_cap.imply.all_el)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(sets.el_cap.given.all_el), \
    Eq[-1].this.lhs.find(Element).apply(sets.el_cap.imply.all_el)

    Eq <<= Eq[-2].this.lhs.apply(algebra.all.imply.et.split, cond=A), Eq[-1].this.rhs.apply(algebra.all.given.et.all.split, cond=A)

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.all.to.infer), Eq[-1].this.rhs.args[0].apply(algebra.all.to.infer)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.apply(sets.el.to.et.st.intersect, index=0, simplify=False), \
    Eq[-1].this.rhs.args[0].lhs.apply(sets.el.to.et.st.intersect, index=0, simplify=False)

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.infer.subs.bool, index=0, invert=True), \
    Eq[-1].this.rhs.args[0].apply(algebra.infer.subs.bool, index=0, invert=True)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.args[1].apply(sets.el.to.et.st.intersect), \
    Eq[-1].this.rhs.args[0].lhs.args[1].apply(sets.el.to.et.st.intersect)

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.infer.to.all, wrt=x), \
    Eq[-1].this.rhs.args[0].apply(algebra.infer.to.all, wrt=x)

    Eq <<= Eq[-2].this.lhs.args[1].apply(algebra.all.to.infer), Eq[-1].this.rhs.apply(algebra.all.to.infer)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.apply(sets.el.to.et.st.complement), \
    Eq[-1].this.rhs.lhs.apply(sets.el.to.et.st.complement)

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.infer.subs.bool, index=1, invert=True), \
    Eq[-1].this.rhs.apply(algebra.infer.subs.bool, index=1, invert=True)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.simplify(), Eq[-1].this.rhs.lhs.simplify()

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.infer.to.all, wrt=x), \
    Eq[-1].this.rhs.apply(algebra.infer.to.all, wrt=x)


if __name__ == '__main__':
    run()

# created on 2021-01-26
