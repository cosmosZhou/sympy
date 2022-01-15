from util import *


@apply
def apply(ge, sgm):
    a, b = ge.of(Greater)
    expr, (k, S[a], S[b]) = sgm.of(Sum)
    return Equal(sgm, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(integer=True, given=True)
    n = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(a > b, Sum[n:a:b](f(n)))

    Eq << algebra.gt.imply.ge.relax.apply(Eq[0])
    Eq << algebra.ge.imply.sum_is_zero.apply(Eq[-1], Eq[1].lhs)


if __name__ == '__main__':
    run()
# created on 2019-07-29
