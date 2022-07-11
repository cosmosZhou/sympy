from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[LessEqual])

    return LessEqual(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import calculus
    x, a, b = Symbol(real=True)
    f, g = Function(shape=(), real=True)

    Eq << apply(All[x:a:b](LessEqual(f(x), g(x))))

    Eq << Eq[0].reversed

    Eq << calculus.all_ge.imply.ge.integral.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2019-01-25
