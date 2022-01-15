from util import *


@apply
def apply(self):
    fx, *limits = self.of(ReducedArgMin[Lamda])
    if fx.shape:
        return Equal(self, Lamda(ReducedArgMin(fx), *limits))

    limit, *limits = limits
    return Equal(self, Lamda(ReducedArgMin(Lamda(fx, limit)), *limits))


@prove
def prove(Eq):
    from axiom import algebra

    m, n = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(m,))
    i = Symbol(integer=True)
    x = Symbol(real=True)
    Eq << apply(ReducedArgMin(Lamda[i:n](f(x))))

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)



if __name__ == '__main__':
    run()
# created on 2021-12-17
