from util import *


@apply
def apply(given, lhs=None):
    x, y = given.of(Equal)    
    return Equal(lhs @ x, lhs @ y)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    X = Symbol.X(real=True, shape=(n, n))
    Y = Symbol.Y(real=True, shape=(n, n))
    t = Symbol.t(real=True, shape=(n,))
    Eq << apply(Equal(X, Y), t)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()