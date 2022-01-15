from util import *


@apply
def apply(self):
    expr, (i, *ab) = self.of(Any)
    from axiom.algebra.all.imply.all.limits.negate import negate
    return Any(expr._subs(i, -i), negate(i, *ab))


@prove
def prove(Eq):
    from axiom import algebra, sets

    i, a, b = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i:a:b](f(i) >= 0))

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[0], simplify=False)

    Eq << algebra.any.imply.any.limits.negate.infinity.apply(Eq[-1])

    Eq << Eq[-1].this.find(Element).apply(sets.el.imply.el.neg)


if __name__ == '__main__':
    run()

from . import infinity
# created on 2019-02-13
