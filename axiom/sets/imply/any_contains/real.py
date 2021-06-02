from util import *


@apply
def apply(x, k=None):
    assert x.is_real
    if k is None:
        k = x.generate_var(integer=True, var='k')

    return Exists[k](Contains(x, Interval(k, k + 1, right_open=True)))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(real=True, given=True)
    Eq << apply(x)

    Eq << ~Eq[-1]

    Eq << sets.all_notcontains.imply.notcontains.apply(Eq[1])

    Eq << Eq[-1].this.rhs.apply(sets.cup.to.interval.reals.right_open)


if __name__ == '__main__':
    run()