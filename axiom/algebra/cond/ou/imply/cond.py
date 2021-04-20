from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    cond, ou = given
    cond = cond.invert()
    for i, c in enumerate(axiom.is_Or(ou)):
        if c == cond:
            conds = [*ou.args]
            del conds[i]
            return Or(*conds)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(shape=(), integer=True)    
    g = Function.g(shape=(), integer=True)

    Eq << apply(Contains(x, S), NotContains(x, S) | (f(x) > g(x)))
    
    Eq <<= Eq[0] & Eq[1]
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])
    
if __name__ == '__main__':
    prove()

