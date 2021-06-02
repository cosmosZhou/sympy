from util import *


@apply
def apply(given, n=None):
    import axiom
    assert given.is_ForAll
    j, zero, i = axiom.limit_is_Interval(given.limits, integer=True)
    assert zero.is_Zero

    intersection = given.function.of(Equal[EmptySet])

    xi, xj = intersection.of(Intersection)
    if not xi.has(i):
        xi = xj
        assert xj.has(i)

    return Equal(abs(Cup[i:n](xi)), Sum[i:n](abs(xi)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True, given=False)

    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)

    Eq << apply(ForAll[j:i](Equal(x[i] & x[j], x[i].etype.emptySet)), n=n)

    Eq << Eq[0].subs(i, 1)

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(*Eq[-1].lhs.args).subs(Eq[-1])

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << Eq.induct.lhs.arg.this.split({n})

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(*Eq[-1].rhs.args)

    Eq << Eq[0].subs(i, n).limits_subs(j, i)

    Eq << sets.all_eq.imply.eq.union.apply(Eq[-1])

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq.induct.rhs.this.split({n})

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq.induct.induct()

    Eq << algebra.suffice.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

