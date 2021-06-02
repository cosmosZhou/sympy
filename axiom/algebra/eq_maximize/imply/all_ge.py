from util import *


@apply
def apply(given): 
    (fx, *limits), M = given.of(Equal[Maximize])
    return ForAll(M >= fx, *limits)


@prove(provable=False)
def prove(Eq):
    M = Symbol.M(real=True)
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    Eq << apply(Equal(M, Maximize[x:0:oo](f(x))))


if __name__ == '__main__':
    run()

