from sympy import *
from axiom.utility import prove, apply
import axiom
from sympy.sets.conditionset import conditionset
from axiom import sets, algebre


@apply(given=True)
def apply(imply):
    function, *limits = axiom.is_Exists(imply)
    assert all(len(limit) == 1 for limit in limits)    
    return function


@prove
def prove(Eq):    
    e = Symbol.e(real=True)
    f = Function.f(nargs=(), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)

    Eq << apply(Exists[e](f(e) > 0))
    
    Eq << algebre.condition.imply.exists.apply(Eq[1], wrt=e)


if __name__ == '__main__':
    prove(__file__)

