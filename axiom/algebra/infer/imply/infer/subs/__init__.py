from util import *


@apply
def apply(given):
    eq, f = given.of(Infer)
    old, new = eq.of(Equal)
    return Infer(eq, f._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    t, f, g = Function(integer=True)
    Eq << apply(Infer(Equal(t(x), y), Equal(f(t(x), y), g(x))))

    Eq << algebra.infer.imply.infer.et.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.subs, swap=True)


if __name__ == '__main__':
    run()
from . import bool
# created on 2018-11-23
