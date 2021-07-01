from util import *


@apply
def apply(self):
    expr, *limits = self.of(Lamda[ReducedMax])
    return Equal(self, ReducedMax(Lamda(expr, *limits).simplify()))


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(shape=(oo, n), real=True)
    Eq << apply(Lamda[i:n](ReducedMax(a[i])))
    
    i = Symbol.i(domain=Range(0, n))    
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)    


if __name__ == '__main__':
    run()