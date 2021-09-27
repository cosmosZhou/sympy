from util import *


@apply
def apply(self, k=None):
    a, b = self.of(Interval)
    assert self.left_open and not self.right_open
    assert a.is_integer and b.is_integer
    if k is None:
        k = self.generate_var(integer=True)    
    return Equal(self, Cup[k:a:b](Interval(k, k + 1, left_open=True)))


@prove
def prove(Eq):
    from axiom import sets

    a, b = Symbol(integer=True)
    Eq << apply(Interval(a, b, left_open=True))

    Eq << Eq[-1].this.rhs.apply(sets.cup.to.interval.left_open)

    


if __name__ == '__main__':
    run()