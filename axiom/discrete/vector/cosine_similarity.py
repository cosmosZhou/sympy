from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy.sets.sets import Interval
from sympy import Symbol

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
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    Eq << apply(x, y)
    
    Eq << Eq[0].lhs.this.expand(free_symbol=i)
    
    Eq << Eq[0].rhs.this.expand(free_symbol=i)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
        

if __name__ == '__main__':
    prove()
