from util import *


@apply(simplify=False)
def apply(given):
    cond, fy = given.of(Suffice)
    return Suffice(cond, cond & fy)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Suffice(Equal(a, 0), Equal(c, 0)))

    Eq << algebra.suffice.imply.suffice.split.et.apply(Eq[1], index=1)


if __name__ == '__main__':
    run()
