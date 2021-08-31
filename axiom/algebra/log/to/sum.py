from util import *


@apply
def apply(self):
    prod = self.of(Log)

    rhs = Sum(self.func(prod.function), *prod.limits)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    j, i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(integer=True)
    Eq << apply(Log(Product[i:n, j:n](f(j, i))))

    Eq << algebra.eq.given.eq.exp.apply(Eq[0])


if __name__ == '__main__':
    run()
