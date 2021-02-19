from axiom.utility import prove, apply
from sympy.core.relational import LessThan
from sympy import Symbol
import axiom
from sympy.functions.elementary.extremum import Max
from axiom import algebre


def quadratic_coefficient(fx, x):
    fx = fx.as_poly(x)
    if fx.degree() != 2:
        return None
    b = fx.coeff_monomial(x)
    a = fx.coeff_monomial(x * x)
    c = fx.coeff_monomial(1)
    return a, b, c


@apply
def apply(*given, quadratic=None):
    greater_than, less_than = given
    x, m = axiom.is_GreaterThan(greater_than)
    _x, M = axiom.is_LessThan(less_than)
    assert x == _x
    a, b, c = quadratic_coefficient(quadratic, x)
    
    assert a > 0
    return LessThan(quadratic, Max(a * m * m + b * m + c, a * M * M + b * M + c))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    m = Symbol.m(real=True)
    M = Symbol.M(real=True)
    
    a = Symbol.a(real=True, positive=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)

    Eq << apply(x >= m, x <= M, quadratic=a * x * x + b * x + c)   
    
    x = Symbol.x(definition=x + b / (2 * a))    
    
    Eq.x_definition = x.this.definition
    
    Eq << Eq.x_definition - Eq.x_definition.rhs.args[1]
    
    Eq.x_original_definition = Eq[-1].reversed
    
    Eq << Eq[0].subs(Eq.x_original_definition)
    
    Eq << Eq[-1] + b / (2 * a)
    
    Eq << Eq[1].subs(Eq.x_original_definition)
    
    Eq << Eq[-1] + b / (2 * a)
    
    Eq << algebre.greater_than.less_than.imply.less_than.square.apply(Eq[-3], Eq[-1])
    
    Eq << Eq[-1].subs(Eq.x_definition)
    
    Eq << Eq[-1] * a
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1] - b * b / (4 * a) + c
    
    Eq << Eq[-1].this.rhs.astype(Max)

    
if __name__ == '__main__':
    prove(__file__)
