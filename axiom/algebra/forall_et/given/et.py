from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, simplify=True):
    et, *limits = axiom.forall_et(given)
    eqs = []
    for eq in et.args:
        forall = ForAll(eq, *limits)
        if simplify:
            forall = forall.simplify()
        eqs.append(forall)
    return And(*eqs)


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)    
    x = Symbol.x(real=True, shape=(k,), given=True)
    
    A = Symbol.A(etype=dtype.real * k)
    y = Symbol.y(real=True, shape=(k,), given=True)
    
    f = Function.f(real=True)
    g = Function.g(real=True)
    b = Symbol.b(shape=(k,), real=True)
    
    Eq << apply(ForAll[x:A](And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b))))
    
    Eq << algebra.et.imply.cond.apply(Eq[1])
    
    Eq << algebra.forall_et.given.forall.apply(Eq[0])

    
if __name__ == '__main__':
    prove()

