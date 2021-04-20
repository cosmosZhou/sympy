from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    et, *limits = axiom.exists_et(given)
    eqs = et.args
    
    eqs = tuple(Exists(eq, *limits) for eq in eqs)
    return And(*eqs)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)
    
    Eq << apply(Exists[x:2:b]((x <= 3) & (f(x) >= 1)))
    
    Eq << algebra.exists_et.imply.exists.split.apply(Eq[0])
    
    Eq << algebra.et.given.cond.apply(Eq[1])


if __name__ == '__main__':
    prove()

