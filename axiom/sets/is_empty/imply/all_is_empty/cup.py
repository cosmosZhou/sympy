from util import *


@apply
def apply(given):
    x_union = given.of(Equal[EmptySet])

    expr, *limits = x_union.of(Cup)
    return All(Equal(expr, x_union.etype.emptySet), *limits)


@prove
def prove(Eq):
    from axiom import sets, algebra
    i = Symbol(integer=True)
    k = Symbol(integer=True, positive=True, given=True)
    x = Symbol(shape=(k + 1,), etype=dtype.integer, given=True)

    Eq << apply(Equal(Cup[i:0:k + 1](x[i]), x[i].etype.emptySet))

    j = Symbol(domain=Range(k + 1))

    Eq << Eq[-1].limits_subs(i, j)

    Eq.paradox = ~Eq[-1]

    Eq.positive = Eq.paradox.this.expr.apply(sets.ne_empty.imply.gt_zero)

    Eq.union_empty = Eq[0].apply(sets.eq.imply.eq.card)

    Eq << sets.eq.imply.eq.complement.apply(Eq[0], Eq.paradox.lhs)

    Eq << Eq[-1].apply(sets.eq.imply.eq.card)

    Eq << sets.imply.eq.principle.add.apply(*Eq[-2].lhs.args)

    Eq << Eq[-1].subs(Eq[-2], Eq.union_empty)

    Eq << algebra.cond.any.imply.any_et.apply(Eq.positive, Eq[-1].reversed)


if __name__ == '__main__':
    run()

# created on 2020-08-09
