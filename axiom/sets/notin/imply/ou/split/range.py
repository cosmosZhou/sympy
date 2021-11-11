from util import *


@apply
def apply(given):
    e, S = given.of(NotElement)
    start, stop = S.of(Range)

    lower_bound = e < start
    upper_bound = e >= stop
    return Or(lower_bound, upper_bound)


@prove
def prove(Eq):
    from axiom import sets
    e, a, b = Symbol(integer=True, given=True)

    Eq << apply(NotElement(e, Range(a, b)))

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(sets.lt.ge.imply.el.range)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

# created on 2021-05-17
# updated on 2021-05-17
