from util import *


@apply
def apply(given):
    eq, f = given.of(Suffice)
    old, new = eq.of(Equal)
    return Suffice(eq, f._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra

    y, x = Symbol(integer=True)
    t, f, g = Function(integer=True)
    Eq << apply(Suffice(Equal(t(x), y), Equal(f(t(x), y), g(x))))

    Eq << algebra.suffice.given.suffice.et.apply(Eq[0])
    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq, index=1)


if __name__ == '__main__':
    run()
from . import bool
