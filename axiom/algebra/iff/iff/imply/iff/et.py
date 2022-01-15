from util import *



@apply
def apply(eq_ab, eq_xy):
    a, b = eq_ab.of(Equivalent)
    x, y = eq_xy.of(Equivalent)
    return Equivalent(a & x, b & y)


@prove
def prove(Eq):
    from axiom import algebra
    a, b, x, y = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Equivalent(a > 0, b > 0), Equivalent(x > 0, y > 0))

    Eq << algebra.iff.given.et.apply(Eq[-1])

    Eq << algebra.iff.imply.infer.apply(Eq[0])

    Eq << algebra.iff.imply.infer.apply(Eq[1])

    Eq << algebra.infer.infer.imply.infer.et.apply(Eq[-2], Eq[-1])

    Eq << algebra.iff.imply.assuming.apply(Eq[0])

    Eq << algebra.iff.imply.assuming.apply(Eq[1])

    Eq << algebra.assuming.assuming.imply.assuming.et.apply(Eq[-2], Eq[-1])

if __name__ == '__main__':
    run()
# created on 2018-03-28
