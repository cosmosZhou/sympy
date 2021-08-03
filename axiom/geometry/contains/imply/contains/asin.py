from util import *


@apply
def apply(contains):
    x, domain = contains.of(Contains)
    a, b = domain.of(Interval)
    assert b <= 1 and a >= -1    
    return Contains(asin(x), Interval(asin(a), asin(b)))


@prove
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(Contains(x, Interval(0, 1)))


if __name__ == '__main__':
    run()