from util import *


@apply
def apply(given):
    e, S = given.of(NotContains)
    start, stop = S.of(Range)

    lower_bound = e < start
    upper_bound = e >= stop
    return Or(lower_bound, upper_bound)


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol.e(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)

    Eq << apply(NotContains(e, Range(a, b)))

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(sets.lt.ge.imply.contains.range)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

