from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Interval)
    assert A.left_open or A.right_open
    return LessEqual(b - a, 0)


@prove
def prove(Eq):
    from axiom import sets
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Equal(Interval(a, b, left_open=True), a.emptySet))
    
    Eq << sets.interval_is_emptyset.given.le.apply(Eq[0])
    
    Eq << Eq[-1] - a


if __name__ == '__main__':
    run()