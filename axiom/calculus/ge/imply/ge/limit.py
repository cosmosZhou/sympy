from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(GreaterEqual)

    return GreaterEqual(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import calculus, algebra
    x, a, b = Symbol(real=True)

    f, g = Function(shape=(), real=True)

    Eq << apply(GreaterEqual(f(x), g(x)), (x, a, b))

    Eq << Eq[0].apply(algebra.cond.imply.all.restrict, (x, a, b))

    Eq << calculus.all_ge.imply.ge.integral.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-05-21
