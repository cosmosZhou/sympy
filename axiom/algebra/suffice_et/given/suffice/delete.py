from util import *


@apply
def apply(given, index=-1):
    [*eqs], rhs = given.of(Suffice[And, Boolean])
    del eqs[index]
    et = And(*eqs)
    return Suffice(et, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    x = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    Eq << apply(Suffice(Equal(f[n], g[n]) & Element(x, A), Equal(f[n + 1], g[n + 1])))

    Eq << algebra.suffice.imply.suffice.et.both_sided.apply(Eq[1], cond=Element(x, A))
    Eq << algebra.suffice.imply.suffice.split.et.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()
