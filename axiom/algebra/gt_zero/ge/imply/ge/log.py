from util import *


@apply
def apply(is_positive, ge):
    x = is_positive.of(Expr > 0)
    lhs, rhs = ge.of(GreaterEqual)
    assert rhs == x
    return GreaterEqual(log(lhs), log(rhs))


@prove
def prove(Eq):
    from axiom import algebra

    x, b = Symbol(real=True)
    Eq << apply(b > 0, x >= b)

    t = Symbol(positive=True)
    Eq << (x >= t).this.apply(algebra.ge.imply.ge.log)

    Eq << algebra.infer.imply.ou.apply(Eq[-1])

    Eq << algebra.cond.imply.ou.subs.apply(Eq[-1], t, b)

    Eq << algebra.cond.ou.imply.cond.apply(Eq[0], Eq[-1])

    Eq << algebra.cond.ou.imply.cond.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-08
