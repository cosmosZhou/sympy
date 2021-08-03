from util import *


@apply
def apply(contains):
    x, domain = contains.of(Contains)
    a, b = domain.of(Interval)
    assert {a, b} in Interval(-1, 1)
    return Contains(acos(x), Interval(acos(b), acos(a), left_open=domain.right_open, right_open=domain.left_open))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(real=True)
    a, b = Symbol(domain=Interval(-1, 1))
    Eq << apply(Contains(x, Interval(a, b, right_open=True)))

    
    Eq << sets.contains.given.et.split.interval.apply(Eq[1])

    


if __name__ == '__main__':
    run()