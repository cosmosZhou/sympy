from util import *


@apply
def apply(self):
    function, *limits, limit = self.of(Maximize)
    
    if limits:
        rhs = ReducedMax(Lamda(Maximize(function, *limits), limit).simplify())
    else:
        rhs = ReducedMax(Lamda(function, limit).simplify())
    
    return Equal(self, rhs, evaluate=False)


@prove(proved=False)
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(shape=(oo, n), real=True)
    Eq << apply(Maximize[i, j](a[i, j]))


if __name__ == '__main__':
    run()