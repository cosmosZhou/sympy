from util import *
import axiom



@apply
def apply(given):
    lhs, rhs = given.of(Equal)    
    return Equal(sqrt(lhs), sqrt(rhs))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    i = Symbol.i(domain=Range(0, n))
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    
    Eq << apply(Equal(f(i), g(i)))
    
    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

