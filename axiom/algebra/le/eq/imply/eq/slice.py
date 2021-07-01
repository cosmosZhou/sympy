from util import *


@apply
def apply(*given):
    less_than, equal = given
    k, n = less_than.of(LessEqual)
    a, b = equal.of(Equal)
    assert a.shape == b.shape
    assert n <= a.shape[0] == b.shape[0]
    
    return Equal(a[:k], b[:k])

@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,))
    y = Symbol.y(real=True, shape=(n,))
    Eq << apply(LessEqual(k, n), Equal(x, y))
    
    Eq << Eq[-1].subs(Eq[1])
    

if __name__ == '__main__':
    run()

