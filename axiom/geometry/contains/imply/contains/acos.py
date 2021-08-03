from util import *


@apply
def apply(contains):
    x, domain_x = contains.of(Contains)
    assert domain_x in Interval(0, 1)
    return Contains(acos(x), Interval(0, S.Pi / 2))


@prove
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(Contains(x, Interval(0, 1)))


if __name__ == '__main__':
    run()