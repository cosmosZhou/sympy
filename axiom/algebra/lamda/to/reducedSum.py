from util import *


@apply
def apply(self):
    expr, *limits = self.of(Lamda[ReducedSum])
    return Equal(self, ReducedSum(Lamda(expr, *self.limits).simplify()))


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(oo, n), real=True)
    Eq << apply(Lamda[i:n](ReducedSum(x[i])))
    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()
# created on 2019-10-21
