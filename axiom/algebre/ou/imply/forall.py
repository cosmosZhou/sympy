from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre


# given: f(a) != f(b) or a = b
# ForAll[a: a!=b](f(a) != f(b)) 
@apply
def apply(given, pivot=0, wrt=None):
    conds = axiom.is_Or(given)
    
    eq = conds.pop(pivot)
    
    if wrt is None:
        wrt = eq.wrt
            
    assert eq._has(wrt)

    cond = eq.invert()
    
    return ForAll[wrt:cond](given.func(*conds))            


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    y = Symbol.y(complex=True, shape=(n,))    
    
    f = Function.f(nargs=(n,), complex=True, shape=())
    g = Function.g(nargs=(n,), complex=True, shape=())

    Eq << apply(Unequal(f(x), g(y)) | Equality(x, y), pivot=1)
    
    Eq << Eq[0].bisect(Equality(x, y)).split()
    
    Eq << ~Eq[-1]
    
    Eq << algebre.imply.forall.limits_assert.apply(Eq[-1].limits)
    
    Eq << Eq[-1].this.function.simplify()
    
    Eq << sets.imply.is_nonemptyset.complement.apply(y, simplify=False)
    
    Eq << sets.is_nonemptyset.forall.imply.exists.apply(Eq[-1], Eq[-2])
    
    Eq << sets.unequal.astype.contains.apply(x, y)
    
    Eq << ForAll[x: Equality(Boole(Contains(x, Eq[2].limits[0][1])), 1)](Eq[2].function, plausible=True)
    
    Eq << Eq[-1].this.limits[0][1].lhs.astype(Piecewise)
    
    Eq << algebre.equivalent.condition.imply.condition.apply(Eq[-2].reversed, Eq[-1])
    
    Eq << Eq[-1].this.limits[0][1].lhs.astype(Piecewise)

    
if __name__ == '__main__':
    prove(__file__)

