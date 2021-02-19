from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
from axiom.algebre.forall.imply.ou.rewrite import rewrite_as_Or


@apply
def apply(imply):
    return rewrite_as_Or(imply)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    f = Function.f(nargs=(), shape=(), integer=True)    
    A = Symbol.A(etype=dtype.integer)
    
    Eq << apply(ForAll[x:A](f(x) > 0))
    
    Eq << algebre.ou.imply.forall.apply(Eq[1], pivot=1, wrt=x)


if __name__ == '__main__':
    prove(__file__)

