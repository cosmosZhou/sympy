from util import *


@apply(given=None)
def apply(gt):
    a, x = gt.of(Greater)
    assert x.is_integer and a.is_integer
    return Equivalent(gt, GreaterEqual(a, x + 1).simplify(), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(x > a)

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(algebra.gt.imply.ge.strengthen), Eq[-1].this.rhs.apply(algebra.gt.given.ge)

    Eq <<= Eq[-2].this.lhs.reversed, Eq[-1].this.rhs.reversed

    Eq <<= Eq[-2].this.lhs + 1, Eq[-1].this.rhs + 1

    


if __name__ == '__main__':
    run()
# created on 2022-01-02
