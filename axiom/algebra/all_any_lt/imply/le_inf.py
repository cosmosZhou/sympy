from util import *


@apply
def apply(given): 
    ((fx, M), *limits), (M, M0_domain) = given.of(All[Any[Less]])
    M0, a = M0_domain.of(Interval)
    assert a.is_Infinity and M0_domain.left_open
    return Inf(fx, *limits) <= M0


@prove
def prove(Eq):
    from axiom import algebra

    M0, a, b = Symbol(real=True, given=True)
    M, x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[M:Interval(M0, oo, left_open=True)](Any[x:a:b](f(x) < M)))

    Eq << ~Eq[1]

    Eq << algebra.gt_inf.imply.any_all_ge.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()