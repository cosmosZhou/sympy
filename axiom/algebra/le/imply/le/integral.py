from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(LessEqual)

    return LessEqual(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    x, a, b = Symbol(real=True)

    f, g = Function(shape=(), real=True)

    Eq << apply(LessEqual(f(x), g(x)), (x, a, b))

    Eq << Eq[0].apply(algebra.cond.imply.all.restrict, (x, a, b))

    Eq << algebra.all_le.imply.le.integral.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-10-31
# updated on 2019-10-31
