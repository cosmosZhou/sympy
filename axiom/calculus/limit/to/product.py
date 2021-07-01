from util import *


from axiom.calculus.limit.to.sum import doit

@apply
def apply(self, simplify=True):
    return Equal(self, doit(Product, self, simplify=simplify), evaluate=False)


@prove(proved=False)
def prove(Eq):
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True)
    s = Function.s(real=True)
    Eq << apply(Limit[n:oo](Product[k:n](s(k))))


if __name__ == '__main__':
    run()