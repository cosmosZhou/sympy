from util import *


@apply
def apply(self):
    expr, *limits = self.of(Lamda[ReducedArgMax])
    return Equal(self, ReducedArgMax(Lamda(expr, *limits).simplify()))


@prove
def prove(Eq):
    from axiom import algebra
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(shape=(oo, n), real=True)
    Eq << apply(Lamda[i:n](ReducedArgMax(a[i])))

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()
# created on 2021-12-20
