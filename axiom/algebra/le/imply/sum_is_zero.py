from util import *


@apply
def apply(le, sgm):
    _b, _a = le.of(LessEqual)
    expr, (k, a, b) = sgm.of(Sum)
    assert _a == a and _b == b
    return Equal(sgm, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(integer=True, given=True)
    n = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(b <= a, Sum[n:a:b](f(n)))

    Eq << algebra.ge.imply.sum_is_zero.apply(Eq[0].reversed, Eq[1].lhs)

    

    


if __name__ == '__main__':
    run()
# created on 2019-11-18
# updated on 2019-11-18
