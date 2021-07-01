from util import *



@apply
def apply(given, index):
    x, S = given.of(Contains)
    a = given.generate_var(**x.type.dict)
    return Any[a:S](Equal(x[index], a[index]))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(positive=True, integer=True)
    x = Symbol.x(integer=True, shape=(n,))
    i = Symbol.i(integer=True)
    S = Symbol.S(etype=dtype.integer * n)

    Eq << apply(Contains(x, S), index=i)

    a = Eq[-1].variable

    Eq << algebra.any.given.any.subs.apply(Eq[-1], a, x)

    Eq << sets.any_contains.given.is_nonemptyset.apply(Eq[-1])

    Eq << sets.contains.imply.is_nonemptyset.apply(Eq[0])


if __name__ == '__main__':
    run()

