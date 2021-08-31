from util import *


@apply
def apply(given): 
    (fx, *limits), M = given.of(Equal[Inf])
    return All(M <= fx, *limits)


@prove
def prove(Eq):
    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(M, Inf[x:a:b](f(x))))


if __name__ == '__main__':
    run()