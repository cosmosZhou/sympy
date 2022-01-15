from util import *


@apply(given=None)
def apply(self):
    expr, (i,) = self.of(Any)
    return Equivalent(self, Any[i](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i, a, b, c = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i](f(i) >= 0))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.any.imply.any.limits.negate.infinity)

    Eq << Eq[-1].this.lhs.apply(algebra.any.imply.any.limits.negate.infinity)


if __name__ == '__main__':
    run()
# created on 2018-07-10
