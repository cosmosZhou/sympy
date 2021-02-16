from sympy import *
from axiom.utility import prove, apply
from axiom.algebre.equal.condition.imply.condition.kronecker_delta import process_given_conditions
import axiom


@apply(given=True)
def apply(imply, **kwargs):
    imply = axiom.is_And(imply)
    eq, cond = imply
    if not eq.is_Equal:
        eq, cond = cond, eq
    eq, f_eq = process_given_conditions(eq, cond, **kwargs)    
    return And(eq, f_eq.simplify())


@prove
def prove(Eq):    
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    f = Function.f(nargs=(2,), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)
    Eq << apply(Equal(x, y) & Unequal(g(KroneckerDelta(x, y)), f(x, y)))
    
    Eq << Equal(KroneckerDelta(x, y), 1, plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[1].split()
    
    Eq << Eq[-1].subs(Eq[2].reversed)
    
    Eq <<= Eq[-1] & Eq[-3]

    
if __name__ == '__main__':
    prove(__file__)

