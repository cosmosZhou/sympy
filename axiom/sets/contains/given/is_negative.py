from util import *


@apply
def apply(given):
    x, R = given.of(Contains)
    [*_] = R.of(Interval[NegativeInfinity, 0])
    
    assert R.right_open
    assert x.is_complex
    return Less(x, 0)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(complex=True, given=True)
    Eq << apply(Contains(x, Interval(-oo, 0, right_open=True)))

    Eq << sets.lt.imply.contains.interval.apply(Eq[1])

    


if __name__ == '__main__':
    run()