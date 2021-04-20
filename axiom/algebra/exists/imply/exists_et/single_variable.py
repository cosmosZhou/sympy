from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply
def apply(given):
    function, *limits = axiom.is_Exists(given)
    assert len(limits) == 1
    variable = limits[0][0]
    cond = given.limits_cond
    assert not cond
    return Exists[variable]((function & cond).simplify())


@prove
def prove(Eq):    
    e = Symbol.e(real=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(Exists[e:g(e) > 0](f(e) > 0))
    
    S = Symbol.S(conditionset(e, g(e) > 0))
    
    Eq << Exists[e:S](f(e) > 0, plausible=True)
    
    Eq << Eq[-1].this.limits[0][1].definition
    
    Eq << sets.exists.imply.exists_et.single_variable.apply(Eq[-1], simplify=False)
    
    Eq << Eq[-1].this.function.args[0].rhs.definition


if __name__ == '__main__':
    prove()

