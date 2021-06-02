from util import *


@apply
def apply(fraction):
    import axiom
    x = fraction.of(FractionalPart)
    x = -x
    x, two = axiom.is_Divide(x)
    assert two == 2

    return Equal(fraction, frac(x / 2))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True)
    Eq << apply(frac(-n / 2))

    Eq << Eq[0].apply(algebra.cond.given.et.all, cond=Equal(n % 2, 0))

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq <<= algebra.imply.all.limits_assert.apply(Eq[-2].limits).this.function.apply(algebra.is_even.imply.any), algebra.imply.all.limits_assert.apply(Eq[-1].limits).this.function.apply(algebra.is_nonzero.imply.any)

    Eq <<= Eq[2] & Eq[-2], Eq[3] & Eq[-1]

    Eq <<= Eq[-2].this.function.apply(algebra.et.given.any_et, simplify=None), Eq[-1].this.function.apply(algebra.et.given.any_et, simplify=None)

    Eq << Eq[-2].this.function.function.apply(algebra.et.given.et.subs.eq, index=1)

    Eq << Eq[-1].this.function.function.apply(algebra.et.given.et.subs.eq, index=1)


if __name__ == '__main__':
    run()
