from util import *


@apply
def apply(self):
    prod = self.of(Log)    
    
    rhs = Sum(self.func(prod.function), *prod.limits)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    j = Symbol.j(integer=True)
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(integer=True)
    Eq << apply(Log(Product[i:n, j:n](f(j, i))))

    Eq << algebra.eq.given.eq.exp.apply(Eq[0])


if __name__ == '__main__':
    run()