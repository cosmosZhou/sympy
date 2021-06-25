from util import *


@apply
def apply(given):
    e, S = given.of(NotContains)
    start, stop = S.of(Interval)

    if S.left_open:
        lower_bound = e <= start
    else:
        lower_bound = e < start
    if S.right_open:
        upper_bound = e >= stop
    else:
        upper_bound = e > stop

    return Or(lower_bound, upper_bound)


@prove
def prove(Eq):
    from axiom import sets

    e = Symbol.e(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(NotContains(e, Interval(a, b)))

    Eq << ~Eq[0]

    
    Eq << sets.contains.imply.et.split.interval.apply(Eq[-1])
    
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()