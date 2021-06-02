

from util import *

@apply
def apply(x, y):
    assert x.shape == y.shape
    assert len(x.shape) == 1
    return Equal(x @ y, y @ x)




@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    x = Symbol.x(shape=(n,), real=True)
    y = Symbol.y(shape=(n,), real=True)
    i = Symbol.i(domain=Range(0, n))
    Eq << apply(x, y)
    
    Eq << Eq[0].lhs.this.expand(var=i)
    
    Eq << Eq[0].rhs.this.expand(var=i)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
        

if __name__ == '__main__':
    run()
