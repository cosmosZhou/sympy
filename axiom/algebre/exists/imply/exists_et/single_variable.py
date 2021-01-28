from sympy import *
from axiom.utility import prove, apply
import axiom
from sympy.sets.conditionset import conditionset
from axiom import sets


@apply(imply=True)
def apply(given):
    function, *limits = axiom.is_Exists(given)
    variable = axiom.limit_is_Boolean(limits)
    return Exists[variable]((function & given.limits_condition).simplify())


@prove
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

