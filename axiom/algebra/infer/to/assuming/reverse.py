from util import *


@apply(given=None)
def apply(given):
    fx, fy = given.of(Infer)
    return Equivalent(given, Assuming(fy, fx))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Infer(f(n) < g(n), f(n + 1) < g(n + 1)))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.infer.imply.assuming.reverse)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.given.assuming.reverse)


if __name__ == '__main__':
    run()
# created on 2019-10-07
