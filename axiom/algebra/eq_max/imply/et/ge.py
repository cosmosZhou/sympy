from util import *


@apply
def apply(given, index=-1): 
    args, M = given.of(Equal[Max])
    first = args[:index]
    second = args[index:]
    return GreaterEqual(M, Max(*first)), GreaterEqual(M, Max(*second))


@prove
def prove(Eq):
    from axiom import algebra

    M = Symbol.M(real=True)
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    Eq << apply(Equal(M, Max(f(x), g(x))))

    Eq << algebra.eq_max.imply.ge.apply(Eq[0], index=0)
    Eq << algebra.eq_max.imply.ge.apply(Eq[0], index=1)

    


if __name__ == '__main__':
    run()