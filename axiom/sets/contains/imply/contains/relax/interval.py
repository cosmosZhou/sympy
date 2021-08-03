from util import *


@apply
def apply(contains):
    x, domain = contains.of(Contains)
    a, b = domain.of(Interval)
    assert domain.left_open and not domain.right_open
    
    b = Ceiling(b)
    
    a = Floor(a)    
    return Contains(x, Interval(a, b, left_open=True))


@prove
def prove(Eq):
    from axiom import sets

    a, b = Symbol(real=True)
    x = Symbol(real=True)
    Eq << apply(Contains(x, Interval(a, b, left_open=True)))

    Eq << Subset(Interval(a, b, left_open=True), Interval(Floor(a), Ceiling(b), left_open=True), plausible=True)

    Eq << sets.subset.given.all_contains.apply(Eq[-1])
    Eq << sets.contains.subset.imply.contains.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()