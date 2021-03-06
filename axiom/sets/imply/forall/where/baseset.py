from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.sets.contains import Contains
from sympy.sets.sets import Interval, CartesianSpace
from sympy import Symbol
from sympy import ForAll
from sympy.core.numbers import oo
from sympy.sets.conditionset import conditionset
from sympy.core.symbol import dtype
from sympy.core.function import Function
# P is condition set;


@apply(imply=True)
def apply(P):
    definition = P.definition
    assert definition.is_ConditionSet    
    x = definition.variable
    
    return ForAll[x:P](definition.condition & Contains(x, definition.base_set))




@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    x = Symbol.x(shape=(oo,), integer=True)
    
    f = Function.f(nargs=(n,), shape=(), integer=True)
    
    P = Symbol.P(definition=conditionset(x[:n], f(x[:n]) > 0, CartesianSpace(Interval(0, m - 1, integer=True), n)))
    Eq << apply(P)
    
    Eq << Eq[-1].split()
    
    Eq << ForAll[x[:n]:P](Contains(x[:n], P), plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[-1].this.function.rhs.definition
    

if __name__ == '__main__':
    prove(__file__)

