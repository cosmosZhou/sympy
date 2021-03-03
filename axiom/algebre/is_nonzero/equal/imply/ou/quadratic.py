from axiom.utility import prove, apply
from sympy.core.relational import Unequal, Equality
from sympy import Symbol, sqrt, Or
from axiom import algebre, sets
import axiom
from axiom.algebre.greater_than.less_than.imply.less_than.quadratic import quadratic_coefficient


@apply
def apply(*given, x=None):
    is_nonzero, eq = given
    if not is_nonzero.is_Unequality:
        is_nonzero, eq = eq, is_nonzero
        
    a = axiom.is_nonzero(is_nonzero)
    fx, rhs = axiom.is_Equal(eq)
    if not rhs.is_Zero:
        fx -= rhs
    
    _a, b, c = quadratic_coefficient(fx, x=x)
    assert a == _a 
    delta = b * b - 4 * a * c
    
    return Or(Equality(x, (-b + sqrt(delta)) / (a * 2)), Equality(x, (-b - sqrt(delta)) / (a * 2)))


@prove
def prove(Eq):
    x = Symbol.x(complex=True, given=True)
    a = Symbol.a(complex=True, given=True)
    b = Symbol.b(complex=True, given=True)
    c = Symbol.c(complex=True, given=True)
    Eq << apply(Unequal(a, 0), Equality(a * x ** 2 + b * x + c, 0), x=x)
    
    x = Symbol.x(x + b / (2 * a))
    Eq << x.this.definition
    
    Eq << Eq[-1] - b / (2 * a)
    
    Eq << Eq[-1].reversed
    
    Eq << Eq[1].subs(Eq[-1])
    
    Eq << Eq[-1].this.lhs.expand()
     
    Eq << algebre.is_nonzero.equal.imply.ou.square.apply(Eq[0], Eq[-1].reversed, x=x)
    
    Eq << Eq[-1].subs(x.this.definition)
    
    Eq << Eq[-1].this.args[0] - b / (2 * a)
    
    Eq << Eq[-1].this.args[0] - b / (2 * a)
    
    Eq << Eq[2].this.args[0].rhs.expand()
    
    Eq << Eq[-1].this.args[0].rhs.expand()
    

if __name__ == '__main__':
    prove(__file__)
