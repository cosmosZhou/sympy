from util import *
import axiom


@apply
def apply(self):
    assert self.is_Stirling
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
    assert x.type[0] == dtype.integer.set
    assert not x.is_set
    n, k = self.args
    i = Symbol('i', integer=True)
 
    return Equal(self, abs(imageset(x[:k], Cup[i:k](FiniteSet(x[i])), self.conditionset(n, k, x))))


@prove(provable=False)
def prove(Eq):
    from sympy.functions.combinatorial.numbers import Stirling
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True, positive=True)
    Eq << apply(Stirling(n, k))


if __name__ == '__main__':
    run()
