from util import *



@apply
def apply(given):
    assert given.is_Equal
    x_union, emptyset = given.args
    if emptyset:
        tmp = emptyset
        emptyset = x_union
        x_union = tmp
        assert emptyset.is_EmptySet

    assert x_union.is_Cup
    return ForAll(Equal(x_union.function, emptyset), *x_union.limits)


@prove
def prove(Eq):
    from axiom import sets, algebra
    i = Symbol.i(integer=True)
    k = Symbol.k(integer=True, positive=True, given=True)
    x = Symbol.x(shape=(k + 1,), etype=dtype.integer, given=True)

    Eq << apply(Equal(Cup[i:0:k + 1](x[i]), x[i].etype.emptySet))

    j = Symbol.j(domain=Range(0, k + 1))

    Eq << Eq[-1].limits_subs(i, j)

    Eq.paradox = ~Eq[-1]

    Eq.positive = Eq.paradox.this.function.apply(sets.is_nonemptyset.imply.is_positive)

    Eq.union_empty = Eq[0].apply(algebra.eq.imply.eq.abs)

    Eq << sets.eq.imply.eq.complement.apply(Eq[0], Eq.paradox.lhs)

    Eq << Eq[-1].apply(algebra.eq.imply.eq.abs)

    Eq << sets.imply.eq.principle.addition.apply(*Eq[-2].lhs.args)

    Eq << Eq[-1].subs(Eq[-2], Eq.union_empty)

    Eq << algebra.cond.any.imply.any_et.apply(Eq.positive, Eq[-1].reversed)


if __name__ == '__main__':
    run()

