from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
import axiom


@apply
def apply(self):
    x, expr, et = axiom.is_ImageSet(self)
    eqs = axiom.is_And(et)
    return Equal(self, Intersection(*(imageset(x, expr, eq) for eq in eqs)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    
    x = Symbol.x(complex=True, shape=(n,))
    f = Function.f(complex=True, shape=(m,))    
    
    g = Function.g(shape=(), real=True)
    h = Function.h(shape=(), real=True)
    
    Eq << apply(imageset(x, f(x), (g(x) > 0) & (h(x) > 0)))
    

if __name__ == '__main__':
    prove(__file__)

