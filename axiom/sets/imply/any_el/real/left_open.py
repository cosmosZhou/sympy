from util import *


@apply
def apply(x, k=None):
    assert x.is_real
    if k is None:
        k = x.generate_var(integer=True, var='k')

    return Any[k](Element(x, Interval(k, k + 1, left_open=True)))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(real=True, given=True)
    Eq << apply(x)

    Eq << ~Eq[-1]

    Eq << sets.all_notin.imply.notin.apply(Eq[1])

    Eq << Eq[-1].this.rhs.apply(sets.cup.to.interval.reals.left_open)


if __name__ == '__main__':
    run()
