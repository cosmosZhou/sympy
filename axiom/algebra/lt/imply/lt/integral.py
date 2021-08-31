from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Less)

    return Less(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    x, a, b = Symbol(real=True)

    f, g = Function(shape=(), real=True)

    Eq << apply(Less(f(x), g(x)), (x, a, b))

    Eq << Eq[0].apply(algebra.cond.imply.all.restrict, (x, a, b))

    Eq << algebra.all_lt.imply.lt.integral.apply(Eq[-1])


if __name__ == '__main__':
    run()

