from util import *


@apply
def apply(given, index=-1):
    [*eqs], rhs = given.of(Infer[And, Boolean])
    del eqs[index]
    et = And(*eqs)
    return Infer(et, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))
    x = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    Eq << apply(Infer(Equal(f[n], g[n]) & Element(x, A), Equal(f[n + 1], g[n + 1])))

    Eq << algebra.infer.imply.infer.et.both_sided.apply(Eq[1], cond=Element(x, A))
    Eq << algebra.infer.imply.infer.split.et.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()
# created on 2019-04-30
