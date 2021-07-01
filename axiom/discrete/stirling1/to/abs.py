from util import *


@apply
def apply(self):
    assert self.is_Stirling1
    
    x = Symbol('x', shape=(oo,), etype=dtype.integer)
    assert x.type[0] == dtype.integer.set
    assert not x.is_set
    n, k = self.args
    i = Symbol('i', integer=True)
    
    condSet = conditionset(x[:k],
                           And(Equal(Cup(x[i], (i, 0, k)), Range(0, n)),
                               Equal(Sum(abs(x[i]), (i, 0, k)), n),
                               All(Greater(abs(x[i]), 0), (i, 0, k))))
    
    return Equal(self, abs(imageset(x[:k], Cup(FiniteSet(x[i]), (i, 0, k)), condSet)))


@prove(provable=False)
def prove(Eq):
    from sympy.functions.combinatorial.numbers import Stirling1
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True, positive=True)
    Eq << apply(Stirling1(n, k))


if __name__ == '__main__':
    run()
