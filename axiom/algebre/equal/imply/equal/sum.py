from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebre, sets


@apply(imply=True)
def apply(given, *limits):    
    lhs, rhs = axiom.is_Equal(given)
    if limits:
        return Equality(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())
    else:
        return Equality(ReducedSum(lhs).simplify(), ReducedSum(rhs).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    assert i.is_integer
    f = Function.f(nargs=(), shape=(), complex=True)
    g = Function.g(nargs=(), shape=(), complex=True)
    
    Eq << apply(Equality(f(i), g(i)), (i, 0, n))
    
    Eq << algebre.equal.imply.equal.invoke.apply(Eq[0], Sum[i:n], simplify=False)    

if __name__ == '__main__':
    prove(__file__)

