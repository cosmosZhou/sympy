from util import *


@apply
def apply(self):
    x, *limits = self.of(Lamda[Exp])
    return Equal(self, Exp(Lamda(x, *limits).simplify()), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(real=True, shape=(n,))
    Eq << apply(Lamda[j:n](Exp(a[j])))

    _j = Symbol('j', domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], _j)

    


if __name__ == '__main__':
    run()
# created on 2022-01-03
