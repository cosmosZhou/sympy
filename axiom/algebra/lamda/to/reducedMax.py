from util import *


@apply
def apply(self):
    expr, *limits = self.of(Lamda[ReducedMax])
    return Equal(self, ReducedMax(Lamda(expr, *limits).simplify()))


@prove
def prove(Eq):
    from axiom import algebra
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(shape=(oo, n), real=True)
    Eq << apply(Lamda[i:n](ReducedMax(a[i])))

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()
# created on 2019-10-20
# updated on 2019-10-20
