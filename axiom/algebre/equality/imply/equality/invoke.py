from axiom.utility import plausible
from sympy.core.relational import Equality
from sympy import Symbol
from sympy.core.function import Function


@plausible
def apply(given, function):    
    assert given.is_Equality
    return Equality(function(given.lhs), function(given.rhs))


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    f = Function.f(nargs=(n,), real=True, shape=(m,))
    x = Symbol.x(real=True, shape=(n,))
    a = Symbol.a(real=True)
    b = Symbol.b(real=True, shape=(n,))
    Eq << apply(Equality(x * a, b), f)
    
    y = Symbol.y(definition=f(a * x)) 
    Eq << y.this.definition
    
    Eq << Eq[-1].this.rhs.subs(Eq[0])
    
    Eq << Eq[-1].subs(Eq[-2])
    
    
if __name__ == '__main__':
    prove(__file__)
