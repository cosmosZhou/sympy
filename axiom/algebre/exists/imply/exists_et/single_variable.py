
from axiom.utility import plausible
from sympy.core.symbol import dtype

from sympy import Symbol
from sympy import Exists
from sympy.core.function import Function
import axiom
from sympy.sets.conditionset import conditionset
from axiom import sets


@plausible
def apply(given):
    function, *limits = axiom.is_Exists(given)
    variable = axiom.limits_is_Boolean(limits)
    return Exists[variable]((function & given.limits_condition).simplify())


from axiom.utility import check


@check
def prove(Eq):    
    e = Symbol.e(real=True)
    f = Function.f(nargs=(), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)

    Eq << apply(Exists[e:g(e) > 0](f(e) > 0))
    
    S = Symbol.S(definition=conditionset(e, g(e) > 0))
    
    Eq << Exists[e:S](f(e) > 0, plausible=True)
    
    Eq << Eq[-1].this.limits[0][1].definition
    
    Eq << sets.exists.imply.exists_et.single_variable.apply(Eq[-1], simplify=False)
    
    Eq << Eq[-1].this.function.args[0].rhs.definition


if __name__ == '__main__':
    prove(__file__)

