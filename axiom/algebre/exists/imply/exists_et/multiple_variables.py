from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre


@apply
def apply(given):
    function, *limits = axiom.is_Exists(given)
    variable = axiom.limits_are_Boolean(limits)
    return Exists[variable]((function & given.limits_condition).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    f = Function.f(nargs=(), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)
    h = Function.h(nargs=(2,), shape=(), integer=True)
    Eq << apply(Exists[x:f(x) > 0, y:g(y) > 0](h(x, y) > 0))
    
    A = Symbol.A(conditionset(x, f(x) > 0))
    B = Symbol.B(conditionset(y, g(y) > 0))
    
    Eq << Exists[x:A, y:B](h(x, y) > 0, plausible=True)
    Eq << Eq[-1].this.limits[0][1].definition
    Eq << Eq[-1].this.limits[1][1].definition
    
    Eq << sets.exists.imply.exists_et.multiple_variables.apply(Eq[-2], simplify=False)
    Eq << Boole(Eq[-1].function).this.arg.args[1].rhs.definition
    Eq << Eq[-1].this.rhs.arg.args[2].rhs.definition
    
    Eq << algebre.equal.imply.equivalent.apply(Eq[-1])
    
    Eq << algebre.equivalent.condition.imply.condition.apply(Eq[-1], Eq[-4])

    
if __name__ == '__main__':
    prove(__file__)
