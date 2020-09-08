from sympy.core.symbol import Symbol
from sympy.utility import plausible
from sympy.core.relational import Equality
from sympy.sets.sets import Interval
from sympy import var

@plausible
def apply(x, y):
    assert x.shape == y.shape
    assert len(x.shape) == 1
    return Equality(x @ y, y @ x)


from sympy.utility import check


@check
def prove(Eq):
    n = var(integer=True).n
    x = Symbol('x', shape=(n,), real=True)
    y = Symbol('y', shape=(n,), real=True)
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    Eq << apply(x, y)
    
    Eq << Eq[0].lhs.this.expand(free_symbol=i)
    
    Eq << Eq[0].rhs.this.expand(free_symbol=i)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
        

if __name__ == '__main__':
    prove(__file__)
