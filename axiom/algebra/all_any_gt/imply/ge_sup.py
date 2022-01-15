from util import *


@apply
def apply(given):
    ((fx, M), *limits), (M, M0_domain) = given.of(All[Any[Greater]])
    a, M0 = M0_domain.of(Interval)
    assert a.is_NegativeInfinity and M0_domain.right_open
    return Sup(fx, *limits) >= M0


@prove
def prove(Eq):
    from axiom import algebra

    M0, a, b = Symbol(real=True, given=True)
    M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[M:Interval(-oo, M0, right_open=True)](Any[x:a:b](f(x) > M)))

    Eq << ~Eq[1]

    Eq << algebra.lt_sup.imply.any_all_le.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-12-30
