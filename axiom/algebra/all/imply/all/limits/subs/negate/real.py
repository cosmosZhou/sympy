from util import *


@apply
def apply(self, old, new):
    from axiom.algebra.all.limits.subs.negate.real import limits_subs
    return limits_subs(All, self, old, new)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:Interval(a, b, left_open=True)](f(x) > 0), x, c - x)

    Eq << algebra.all.imply.ou.subs.apply(Eq[0], x, c - x)

    Eq << Eq[-1].this.args[0].apply(sets.notin.imply.notin.neg)

    Eq << Eq[-1].this.args[0].apply(sets.notin.imply.notin.add, c)
    Eq << algebra.ou.imply.all.apply(Eq[-1], pivot=1, wrt=x)


if __name__ == '__main__':
    run()