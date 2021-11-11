from util import *


@apply
def apply(given):
    from sympy.concrete.limits import limits_dict

    (xi, limit), (_xi, _limit) = given.of(Equal[Card[Cup], Sum[Card]])

    assert xi == _xi
    assert limit == _limit
    i, _0, n = limit
    assert _0 == 0

    j = xi.generate_var(integer=True)
    xj = xi.subs(i, j)

    return All[j:i, i:n](Equal(xi & xj, xi.etype.emptySet))


@prove
def prove(Eq):
    from axiom import sets, algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(Equal(Card(Cup[i:n](x[i])), Sum[i:n](Card(x[i]))))

    j = Eq[-1].variables[0]
    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(sets.ne_empty.imply.gt_zero)

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(x[i], x[j])

    Eq << Eq[-2].this.expr.apply(algebra.eq.gt.imply.lt.subs, Eq[-1])

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0], Eq[-1], simplify=False)

    Eq.gt = Eq[-1].this.expr.apply(algebra.eq.lt.imply.gt.substract)

    Eq << Eq[0].lhs.arg.this.apply(sets.cup.to.union.split, cond={i, j})

    Eq.union_less_than = sets.imply.le.cup.apply(x[i], *Eq[-1].rhs.args[0].limits)

    Eq << sets.imply.le.union.apply(*Eq[-1].rhs.args)

    Eq << Eq.gt.this.expr.apply(algebra.gt.le.imply.gt.subs, Eq[-1])

    Eq << Eq[-1].this().find(Intersection).simplify()

    Eq << Eq[-1].this.find(Card + Card[~Cup]).apply(sets.cup.to.union.doit.setlimit)

    Eq << Eq.union_less_than.this.find(Cup).limits_subs(Eq.union_less_than.find(Cup).variable, Eq[-1].find(Cup).variable)

    Eq << Eq[-1].this.expr.apply(algebra.gt.le.imply.gt.subs, Eq.union_less_than)

    Eq << Eq[-1].this().expr.lhs.simplify()


if __name__ == '__main__':
    run()


from . import complement
# created on 2021-03-19
# updated on 2021-03-19
