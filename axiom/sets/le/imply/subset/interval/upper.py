from util import *


@apply
def apply(given, upper, left_open=False, right_open=False):
    a, b = given.of(LessEqual)
    kwargs = {'right_open' : right_open, 'left_open': left_open}
    return Subset(Interval(b, upper, **kwargs), Interval(a, upper, **kwargs))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x <= y, z, left_open=True)

    Eq << sets.subset.given.all_el.apply(Eq[1])

    Eq << Eq[-1].this.expr.apply(sets.el_interval.given.et)

    Eq << algebra.all_et.given.et.all.apply(Eq[-1])

    Eq <<= algebra.all.given.ou.apply(Eq[-2]), algebra.all.given.ou.apply(Eq[-1])

    Eq <<= Eq[-2].this.args[1].apply(sets.notin_interval.given.ou), Eq[-1].this.args[0].apply(sets.notin_interval.given.ou)

    Eq << algebra.ou.given.ou.apply(Eq[-1], slice(0, 3, 2))

    Eq << sets.ou.given.notin.interval.apply(Eq[-1])

    Eq << sets.le.imply.interval_is_empty.apply(Eq[0], left_open=True)

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-09-06
