from util import *


@apply
def apply(self, old, new):
    from axiom.algebra.all.limits.subs.negate.real import limits_subs
    return limits_subs(Any, self, old, new)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Any[x:Interval(a, b, left_open=True)](f(x) > 0), x, c - x)

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[0], simplify=None)

    Eq << algebra.any.imply.any.limits.negate.infinity.apply(Eq[-1])

    Eq << Eq[-1].this.find(Element).apply(sets.el.imply.el.neg)

    Eq << algebra.any.imply.any.limits.subs.offset.apply(Eq[-1], -c)


if __name__ == '__main__':
    run()
# created on 2019-02-17
