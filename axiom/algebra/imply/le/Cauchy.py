from util import *


@apply
def apply(a, b):
    assert len(a.shape) == len(b.shape) == 1
    return ReducedSum(a * b) ** 2 <= ReducedSum(a ** 2) * ReducedSum(b ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(domain=Range(2, oo))
    a, b = Symbol(shape=(n,), real=True, given=True)
    Eq << apply(a, b)

    x = Symbol(real=True)
    Eq << ReducedSum((x * a + b) ** 2).this.arg.apply(algebra.square.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.reducedSum.to.add)

    Eq << GreaterEqual(Eq[-1].lhs, 0, plausible=True)

    Eq << algebra.eq.ge.imply.ge.add.apply(Eq[-2].reversed, Eq[-1])

    Eq << ~Eq[-1]

    Eq << algebra.any_lt_zero.given.add_gt_zero.apply(Eq[-1])

    Eq << Eq[-1] / 4

    Eq << Eq[-1].this.apply(algebra.gt.transport, lhs=0)

    Eq << ~Eq[-1]

    
    


if __name__ == '__main__':
    run()
# created on 2022-04-02
# updated on 2022-04-03
