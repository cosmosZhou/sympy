from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
from axiom.algebra.forall.imply.ou import rewrite_as_Or


@apply
def apply(given, old, new):
    assert old in given.variables
    ou = rewrite_as_Or(given)
    return ou._subs(old, new)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)    
    a = Symbol.a(integer=True, positive=True)
    
    y = Symbol.y(integer=True)
    f = Function.f(shape=(), integer=True)    
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    Eq << apply(ForAll[x:A, y:B](f(x, y) > 0), x, a)
    
    Eq << algebra.forall.imply.ou.apply(Eq[0])
    
    Eq << Eq[-1].subs(x, a)
#     


if __name__ == '__main__':
    prove()

