from util import *
from axiom.calculus.limit.to.sum import doit


@apply
def apply(self, simplify=True):
    return Equal(self, doit(Cup, self, simplify=simplify), evaluate=False)


@prove(proved=False)
def prove(Eq):
    k, n = Symbol(integer=True)
    s = Function(etype=dtype.integer)

    Eq << apply(Limit[n:oo](Cup[k:n](s(k))))


if __name__ == '__main__':
    run()
