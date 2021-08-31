from util import *


@apply
def apply(self):
    expr, *limits = self.of(Lamda[ReducedMin])
    return Equal(self, ReducedMin(Lamda(expr, *limits).simplify()))


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(shape=(oo, n), real=True)
    Eq << apply(Lamda[i:n](ReducedMin(a[i])))
    i = Symbol(domain=Range(0, n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)



if __name__ == '__main__':
    run()
