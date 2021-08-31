from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[LessEqual])

    return LessEqual(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True)

    Eq << apply(All[i:n](LessEqual(f(i), g(i))))

    Eq << Eq[0].reversed

    Eq << algebra.all_ge.imply.ge.sum.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

