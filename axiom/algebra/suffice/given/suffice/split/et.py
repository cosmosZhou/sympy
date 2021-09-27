from util import *


@apply(simplify=False)
def apply(given, index=0):
    eqs, fy = given.of(Suffice)
    cond = eqs.of(And)
    cond = cond[index]
    if isinstance(index, slice):
        cond = And(*cond)
            
    return Suffice(cond, fy)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Suffice(Equal(a, 0) & Equal(b, 0), Equal(c, 0)), index=1)

    Eq << algebra.suffice.imply.suffice.et.both_sided.apply(Eq[1], cond=Equal(a, 0))

    Eq << algebra.suffice.imply.suffice.split.et.apply(Eq[-1], 1)


if __name__ == '__main__':
    run()