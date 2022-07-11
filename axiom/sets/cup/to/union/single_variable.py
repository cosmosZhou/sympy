from util import *


@apply
def apply(self):
    fx, (x, s) = self.of(Cup)
    return Equal(self, fx.as_multiple_terms(x, s, cls=Cup))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)

    Eq << apply(Cup[x:B](Piecewise((f(x, y), Element(x, A)), (g(x, y), True))))

    Eq << sets.eq.given.et.infer.apply(Eq[0], wrt='y')

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cup.imply.any_el), \
    Eq[-1].this.rhs.apply(sets.el_cup.given.any_el)

    Eq <<= Eq[-2].this.lhs.expr.apply(sets.el_piece.imply.ou), \
    Eq[-1].this.rhs.expr.apply(sets.el_piece.given.ou)

    Eq <<= Eq[-2].this.lhs.apply(algebra.any_ou.imply.ou.any), \
    Eq[-1].this.rhs.apply(algebra.any_ou.given.ou.any)

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.any_et.imply.any.limits_absorb, index=0), \
    Eq[-1].this.rhs.args[0].apply(algebra.any_et.given.any.limits_absorb, index=0)

    Eq <<= Eq[-2].this.lhs.args[1].apply(algebra.any_et.imply.any.limits_absorb, index=0), \
    Eq[-1].this.rhs.args[1].apply(algebra.any_et.given.any.limits_absorb, index=0)

    Eq <<= Eq[-2].this.rhs.apply(sets.el_union.given.ou, simplify=None), \
    Eq[-1].this.lhs.apply(sets.el_union.imply.ou, simplify=None)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(sets.el_cup.given.any_el), \
    Eq[-1].this.lhs.find(Element).apply(sets.el_cup.imply.any_el)

    Eq << Eq[-2].this.rhs.find(Element).apply(sets.el_cup.given.any_el)

    Eq << Eq[-1].this.lhs.find(Element).apply(sets.el_cup.imply.any_el)


if __name__ == '__main__':
    run()

# created on 2018-10-03
