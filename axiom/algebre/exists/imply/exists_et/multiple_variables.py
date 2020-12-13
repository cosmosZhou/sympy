from axiom.utility import plausible
from sympy import Symbol
from sympy import Exists
from sympy.core.function import Function
import axiom
from sympy.sets.conditionset import conditionset
from axiom import sets, algebre


@plausible
def apply(given):
    function, *limits = axiom.is_Exists(given)
    variable = axiom.limits_are_Boolean(limits)
    return Exists[variable]((function & given.limits_condition).simplify())


from axiom.utility import check


@check
def prove(Eq):
    from axiom.sets.contains.imply.equality.piecewise.expr_swap import bool
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    f = Function.f(nargs=(), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)
    h = Function.h(nargs=(2,), shape=(), integer=True)
    Eq << apply(Exists[x:f(x) > 0, y:g(y) > 0](h(x, y) > 0))
    
    A = Symbol.A(definition=conditionset(x, f(x) > 0))
    B = Symbol.B(definition=conditionset(y, g(y) > 0))
    
    Eq << Exists[x:A, y:B](h(x, y) > 0, plausible=True)
    Eq << Eq[-1].this.limits[0][1].definition
    Eq << Eq[-1].this.limits[1][1].definition
    
    Eq << sets.exists.imply.exists_et.multiple_variables.apply(Eq[-2], simplify=False)
    Eq << bool(Eq[-1].function).this.arg.args[1].rhs.definition
    Eq << Eq[-1].this.rhs.arg.args[2].rhs.definition
    
    Eq << algebre.equality.exists.imply.exists.apply(Eq[-1], Eq[-3])

    
if __name__ == '__main__':
    prove(__file__)
