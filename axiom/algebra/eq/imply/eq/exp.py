from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)    
    return Equal(exp(lhs), exp(rhs))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    i = Symbol.i(domain=Range(0, n))
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Equal(f(i), g(i)))
    
    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

