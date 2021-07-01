from util import *


from axiom.calculus.limit.to.sum import doit


@apply
def apply(self, simplify=True):                
    return Equal(self, doit(Cap, self, simplify=simplify), evaluate=False)


@prove(proved=False)
def prove(Eq):
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True)
    s = Function.s(etype=dtype.integer)
    Eq << apply(Limit[n:oo](Cap[k:n](s(k))))


if __name__ == '__main__':
    run()