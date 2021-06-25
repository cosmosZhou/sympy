from util import *


@apply
def apply(self):
    [*args], *limits = self.of(Lamda[Add])
    rhs = Add(*(self.func(f, *limits).simplify() for f in args))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(shape=(n, n), real=True)
    y = Symbol.y(shape=(n, n), real=True)
    Eq << apply(Lamda[i:n](x[j, i] + y[i, j]))

    i = Symbol.i(domain=Range(0, n))    
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()
