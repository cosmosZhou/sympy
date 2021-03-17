from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given):
    et, *limits = axiom.forall_et(given)
    eqs = et.args
    
    eqs = tuple(ForAll(eq, *limits)for eq in eqs)
    
    return And(*eqs)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)
    
    Eq << apply(ForAll[x:2:b]((x <= 3) & (f(x) >= 1)))
    
    Eq << algebre.et.given.cond.apply(Eq[1])
    
    Eq << algebre.forall_et.imply.forall.apply(Eq[0])


if __name__ == '__main__':
    prove(__file__)

