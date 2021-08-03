from util import *



@apply
def apply(given):
    x = given.of(Unequal[0])
    assert x.is_nonnegative
    return Greater(x, 0)


@prove
def prove(Eq):
    from axiom import sets
    a = Symbol.a(real=True, nonnegative=True)

    Eq << apply(Unequal(a, 0))

    Eq << Contains(a, Interval(0, oo), plausible=True)

    Eq << sets.ne.imply.notcontains.apply(Eq[0], simplify=False)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

