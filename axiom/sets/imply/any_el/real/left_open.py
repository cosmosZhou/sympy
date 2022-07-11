from util import *


@apply
def apply(x, k=None):
    assert x.is_real
    if k is None:
        k = x.generate_var(integer=True, var='k')

    return Any[k](Element(x, Interval(k, k + 1, left_open=True)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(real=True, given=True)
    Eq << apply(x)

    Eq << algebra.any.given.cond.subs.apply(Eq[0], Eq[0].variable, Ceiling(x) - 1)

    Eq << sets.el_interval.given.et.apply(Eq[-1])

    Eq << algebra.imply.gt.ceiling.apply(x)

    Eq << algebra.imply.le.ceiling.apply(x)


if __name__ == '__main__':
    run()
# created on 2018-10-29
