from util import *


@apply
def apply(le, M=None):
    (fx, *limits), M0 = le.of(Inf > Expr)
    if M is None:
        M = le.generate_var(real=True, var='M')
    return Any[M:Interval(M0, oo, left_open=True)](All(fx >= M, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    M, M0, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:Interval(a, b, left_open=True, right_open=True)](f(x)) > M0, M)

    Eq << algebra.gt_inf.imply.any_all_gt.apply(Eq[0])

    Eq << Eq[-1].this.expr.expr.apply(algebra.gt.imply.ge.relax)


if __name__ == '__main__':
    run()