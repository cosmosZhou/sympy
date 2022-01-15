from util import *


@apply(given=None)
def apply(self):
    expr, (i, *ab) = self.of(Any)
    from axiom.algebra.all.imply.all.limits.negate import negate
    return Equivalent(self, Any(expr._subs(i, -i), negate(i, *ab)))


@prove
def prove(Eq):
    from axiom import algebra

    i, a, b = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i:a:b](f(i) >= 0))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.any.imply.any.limits.negate)

    Eq << Eq[-1].this.lhs.apply(algebra.any.given.any.limits.negate)


if __name__ == '__main__':
    run()

from . import infinity
# created on 2019-02-19
