from util import *


@apply
def apply(self):
    [*args], *limits = self.of(Lamda[Add])
    rhs = Add(*(self.func(f, *limits).simplify() for f in args))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n, n), real=True)
    Eq << apply(Lamda[i:n](x[j, i] + y[i, j]))

    i = Symbol(domain=Range(0, n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()
