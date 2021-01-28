from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom
from axiom.algebre.greater_than.less_than.imply.less_than.quadratic import quadratic_coefficient


@apply(imply=True)
def apply(*given, x=None):
    is_nonzero, eq = given
    if not is_nonzero.is_Unequality:
        is_nonzero, eq = eq, is_nonzero
        
    a = axiom.is_nonzero(is_nonzero)
    fx, rhs = axiom.is_Equal(eq)
    if not rhs.is_Zero:
        fx -= rhs
    
    _a, b, c = quadratic_coefficient(fx, x=x)
    assert b.is_Zero
    assert a == _a 
    delta = -4 * a * c
    
    return Or(Equality(x, sqrt(delta) / (a * 2)), Equality(x, -sqrt(delta) / (a * 2)))


@prove
def prove(Eq):
    x = Symbol.x(complex=True, given=True)
    a = Symbol.a(complex=True, given=True)
    c = Symbol.c(complex=True, given=True)
    Eq << apply(Unequal(a, 0), Equality(a * x ** 2 + c, 0), x=x)
    
    Eq << Eq[1] - c
    
    Eq << algebre.is_nonzero.equal.imply.equal.scalar.apply(Eq[0], Eq[-1])
    
    t = Symbol.t(definition=sqrt(-c / a))
    Eq << t.this.definition
    
    Eq.t_squared = Eq[-1] ** 2
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[-2], Eq.t_squared)
    
    Eq << Eq[-1] - Eq[-1].rhs
    
    Eq << Eq[-1].this.lhs.factor()
    
    Eq << algebre.is_zero.imply.ou.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[1].reversed
    
    Eq.ou = Eq[-1].this.args[0] - t
    
    Eq << -Eq.t_squared * a
    
    Eq << Eq[-1].reversed
    
    Eq << Eq[2].subs(Eq[-1])
    
    Eq << sqrt(a * a * t * t).this.simplify()
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << algebre.ou.given.equal.abs.apply(Eq[-1])
    
    Eq << algebre.ou.imply.equal.abs.apply(Eq.ou)
    
    
if __name__ == '__main__':
    prove(__file__)
