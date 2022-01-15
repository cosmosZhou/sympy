from util import *


@apply
def apply(given, n=None):
    (xi, xj), (j, i) = given.of(All[Equal[Intersection, EmptySet], Tuple[0, Expr]])

    if not xi.has(i):
        xi, xj = xj, xi

    assert xi.has(i)
    assert xj.has(j)

    return Equal(Card(Cup[i:n](xi)), Sum[i:n](Card(xi)))


@prove
def prove(Eq):
    from axiom import sets, algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(shape=(oo,), etype=dtype.integer, finite=True)
    Eq << apply(All[j:i](Equal(x[i] & x[j], x[i].etype.emptySet)), n=n)

    Eq << Eq[0].subs(i, 1)

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(*Eq[-1].lhs.args).subs(Eq[-1])

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << Eq.induct.lhs.arg.this.apply(sets.cup.to.union.split, cond={n})

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(*Eq[-1].rhs.args)

    Eq << Eq[0].subs(i, n).limits_subs(j, i)

    Eq << sets.all_eq.imply.eq.union.apply(Eq[-1])

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq.induct.rhs.this.apply(algebra.sum.to.add.split, cond={n})

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Infer(Eq[1], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2020-12-23
