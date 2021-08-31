from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)    
    return Equal(sqrt(lhs), sqrt(rhs))


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(domain=Range(0, n))
    f, g = Function(shape=(), integer=True)
    Eq << apply(Equal(f(i), g(i)))

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

