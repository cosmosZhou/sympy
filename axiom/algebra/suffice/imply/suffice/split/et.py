from util import *


@apply
def apply(given, index=0):
    fx, fy = given.of(Suffice)
    eqs = fy.of(And)

    if isinstance(index, slice):
        eqs = eqs[index]
        return tuple(Suffice(fx, eq) for eq in eqs)
    return Suffice(fx, eqs[index])


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    f, h, g = Function(integer=True)
    Eq << apply(Suffice(Equal(h(x), h(y)), Equal(f(x), f(y)) & Equal(g(x), g(y))), index=0)

    Eq << Eq[0].this.rhs.apply(algebra.et.imply.cond, index=0)


if __name__ == '__main__':
    run()

