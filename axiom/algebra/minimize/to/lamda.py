from util import *


@apply
def apply(self):
    function, *limits, limit = self.of(Minimize)
    
    if limits:
        rhs = ReducedMin(Lamda(Minimize(function, *limits), limit).simplify())
    else:
        rhs = ReducedMin(Lamda(function, limit).simplify())
    
    return Equal(self, rhs, evaluate=False)


@prove(proved=False)
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(shape=(oo, n), real=True)
    Eq << apply(Minimize[i, j](a[i, j]))


if __name__ == '__main__':
    run()