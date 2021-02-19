
from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol
from sympy.integrals.integrals import Integral


@apply
def apply(n, a=0, b=None, x=None):
    assert n.is_integer
    
    if x is None:
        x = Symbol.x(real=True)
    
    return Equality(Integral(x ** n, (x, a, b)), (b ** (n + 1) - a * (n + 1)) / (n + 1))


@prove
def prove(Eq):    

    x = Symbol.x(real=True)
    n = Symbol.n(integer=True, nonnegative=True)

    Eq << apply(n, b=x)
    
    f = Symbol.f(definition=Eq[0].lhs)
    g = Symbol.g(definition=Eq[0].rhs)
    from sympy import diff
    Eq << diff(f, x).this.expr.definition
    
    Eq << Eq[-1].this.rhs.doit()
    
    Eq.df = Eq[-1].this.rhs.powsimp()
    
    Eq << diff(g, x).this.expr.definition

    Eq << Eq[-1].this.rhs.doit()
    
    Eq << Eq[-1].this.rhs.powsimp()
    
    Eq << Eq.df - Eq[-1]
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq.equality = Eq[-1].this.rhs.args[1].definition
    
    Eq << Eq.equality.subs(x, 0)
    
    Eq << Eq.equality.subs(Eq[-1].reversed).reversed
    
    
if __name__ == '__main__':
    prove(__file__)

