from util import *


@apply
def apply(x, n):
    assert n.is_integer and n > 0
    return Infer(Equal(x ** n, 0), Equal(x, 0))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(complex=True, given=True)
    Eq << apply(x, n)

    Eq << Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.lhs.apply(algebra.pow.to.mul.split.exponent)

    Eq << Eq[-1].this.lhs.apply(algebra.mul_is_zero.imply.ou.is_zero)

    Eq << algebra.infer.given.et.infer.split.ou.apply(Eq[-1])

    Eq << Infer(Eq[0], Eq.induct, plausible=True)
    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()
# created on 2018-11-02
