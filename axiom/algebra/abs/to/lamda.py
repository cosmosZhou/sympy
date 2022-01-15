from util import *


@apply
def apply(self):
    x, *limits = self.of(Abs[Lamda])
    return Equal(self, Lamda(Abs(x), *limits))


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(abs(Lamda[i:n](x[i])))

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)



if __name__ == '__main__':
    run()
# created on 2021-12-21
