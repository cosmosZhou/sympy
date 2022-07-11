from util import *


@apply
def apply(x, n=None):
    if n is None:
        n = x.generate_var(integer=True)
    assert x.is_real
    return Any[n](Element(n, Interval(x - 1, x, left_open=True)))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(x, n)

    Eq << Eq[-1].this.expr.apply(sets.el_interval.given.et)

    Eq << Eq[-1].this.find(Greater) + 1

    Eq << Eq[-1].this.expr.apply(sets.gt.le.given.el)

    Eq << sets.imply.any_el.real.apply(x, n)


if __name__ == '__main__':
    run()

# created on 2021-04-21
