from sympy import *
from axiom.utility import prove, apply


@apply
def apply(given, function): 
    assert given.is_Equality    
    assert function(given.lhs).domain_definition()
    assert function(given.rhs).domain_definition()
    
    return Equality(function(given.lhs), function(given.rhs))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    f = Function.f(nargs=(n,), real=True, shape=(m,))
    x = Symbol.x(real=True, shape=(n,))
    a = Symbol.a(real=True)
    b = Symbol.b(real=True, shape=(n,))
    Eq << apply(Equality(x * a, b), f)
    
    y = Symbol.y(f(a * x)) 
    Eq << y.this.definition
    
    Eq << Eq[-1].this.rhs.subs(Eq[0])
    
    Eq << Eq[-1].subs(Eq[-2])
    
    
if __name__ == '__main__':
    prove(__file__)
