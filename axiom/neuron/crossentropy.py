from sympy.core.symbol import Symbol
from sympy.core.relational import Equality
import sympy
from sympy.functions.elementary.exponential import softmax
from sympy.core.function import Derivative
from sympy.sets.sets import Interval
from sympy.utility import check, plausible, Sum, Ref
from sympy.core.numbers import oo
from sympy.concrete import summations


@plausible
def apply(given):
    assert isinstance(given, Equality)
    lhs = given.lhs
    assert isinstance(lhs, summations.Sum)
    
    limit = lhs.limits[0]
    j, a, b = limit
    n = b - a + 1
    
    t = Ref[j:0:n - 1](lhs.function).simplify()    
    
    assert n >= 2
    
    x = Symbol('x', shape=(n,), real=True)    
    y = Symbol('y', shape=(n,), definition=softmax(x))
    
    L = Symbol('L', definition=-t @ sympy.log(y))
    
    return Equality(Derivative(L, x), y - t, given=given)


@check
def prove(Eq):
    n = Symbol('n', domain=Interval(2, oo, integer=True))    
    t = Symbol('t', shape=(n,), real=True)
    j = Symbol('j', integer=True)
    given = Equality(Sum[j:0:n - 1](t[j]), 1)
    
    Eq << apply(given)
        
    Eq << Eq[1].expand(free_symbol=j)
    
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    xi = Eq[-2].lhs._wrt_variables[0][i]

    assert Eq[1].lhs.has(xi)
    
    Eq << Eq[-1].diff(xi)
    
    Eq.loss = Eq[-1].this.rhs.doit(deep=False)            
    
    i = xi.indices[0]
    Eq << Eq[0][i]
    Eq << Eq[0][j]
    Eq << Eq[-1].diff(xi).this.rhs.doit(deep=False)
    
    Eq << Eq[-1].subs(Eq[-2].reversed).subs(Eq[-3].reversed) / Eq[-1].lhs.expr

    Eq.loss = Eq.loss.subs(Eq[-1]).expand()
    
    Eq.loss = Eq.loss.this.rhs.args[0].simplify()
    
    Eq.loss = Eq.loss.this.rhs.args[1].args[1].simplify()
    
    Eq.loss = Eq.loss.subs(given)
    
    Eq.loss = Eq.loss.reference((i,))

    
if __name__ == '__main__':
    prove(__file__)
