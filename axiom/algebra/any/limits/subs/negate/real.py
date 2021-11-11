from util import *


@apply(given=None)
def apply(self, old, new):
    from axiom.algebra.all.limits.subs.negate.real import limits_subs
    return Equivalent(self, limits_subs(Any, self, old, new), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Any[x:Interval(a, b, right_open=True)](f(x) > 0), x, c - x)

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.any.imply.any.limits.subs.negate.real, x, c - x)
    Eq << Eq[-1].this.rhs.apply(algebra.any.imply.any.limits.subs.negate.real, x, c - x)


if __name__ == '__main__':
    run()
# created on 2019-02-20
# updated on 2019-02-20
