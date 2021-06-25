from util import *


@apply
def apply(self):
    function, *limits = self.of(Maximize[Exp])    
    rhs = exp(Maximize(function, *limits).simplify()).simplify()
    
    return Equal(self, rhs, evaluate=False)


@prove(proved=False)
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(shape=(oo, n), real=True)
    Eq << apply(Maximize[i, j](exp(a[i, j])))


if __name__ == '__main__':
    run()