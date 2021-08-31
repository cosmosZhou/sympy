from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    assert x.is_nonpositive
    return Less(x, 0)


@prove
def prove(Eq):
    from axiom import sets

    a = Symbol(real=True, nonpositive=True)
    Eq << apply(Unequal(a, 0))

    Eq << Element(a, Interval(-oo, 0), plausible=True)

    Eq << sets.ne.imply.notin.apply(Eq[0], simplify=False)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()
