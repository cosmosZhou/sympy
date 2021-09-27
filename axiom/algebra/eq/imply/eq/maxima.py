from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)

    return Equal(Maxima(lhs, *limits).simplify(), Maxima(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(0, n))
    f, g = Function(real=True)
    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], Maxima[i:n], simplify=False)


if __name__ == '__main__':
    run()

