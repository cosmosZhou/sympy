from sympy import *
from axiom.utility import prove, apply
import axiom
from sympy.sets.conditionset import conditionset
from axiom import sets, algebre


@apply
def apply(imply):
    function, *limits = axiom.is_Exists(imply)
    variable = axiom.limits_are_Boolean(limits)
    return Exists[variable]((function & imply.limits_condition).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    f = Function.f(nargs=(), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)
    h = Function.h(nargs=(2,), shape=(), integer=True)
    Eq << apply(Exists[x:f(x) > 0, y:g(y) > 0](h(x, y) > 0))
    
    Eq << algebre.exists_et.imply.exists.limits_absorb.apply(Eq[-1], index=0)
    
    Eq << algebre.exists_et.imply.exists.limits_absorb.apply(Eq[-1], index=0)

    
if __name__ == '__main__':
    prove(__file__)
