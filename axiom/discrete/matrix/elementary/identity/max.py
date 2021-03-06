from sympy import *
from axiom.utility import prove, apply
from axiom import algebre


@apply(imply=True)
def apply(n):    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
     
    return Equality(LAMBDA[j:n, i:n](Piecewise((i, j < i), (j, j > i), (0, True))),
                    (1 - Identity(n)) * LAMBDA[j:n, i:n](Max(i, j)))


@prove
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)

    i = Symbol.i(domain=Interval(0, n - 1, integer=True))    
    j = Symbol.j(domain=Interval(0, n - 1, integer=True))
    
    Eq << algebre.equal.given.equal.getitem.apply(Eq[0], (i, j))
    
    Eq << Eq[-1].this.rhs.args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.simplify(wrt=i)
    
    Eq << Eq[-1].this.rhs.args[0].cond.reversed
    
    Eq << Eq[-1].this.rhs.args[0].expr.args[1].args[1].args[1].astype(Piecewise)    
    
    Eq << Eq[-1].this.rhs.args[0].expr.args[1].args[1].astype(Piecewise, simplify=False)
    
    Eq << Eq[-1].this.rhs.args[0].expr.args[1].astype(Piecewise, simplify=False)
    
    Eq << Eq[-1].this.rhs.args[0].expr.astype(Piecewise, simplify=False)
    
    Eq << Eq[-1].this.rhs.apply(algebre.imply.equal.piecewise.flatten, index=0)
    
    Eq << Eq[-1].this.rhs.apply(algebre.imply.equal.piecewise.swap.front)
    
    Eq << Eq[-1].this.lhs.apply(algebre.imply.equal.piecewise.swap.back)
    
    Eq << Eq[-1].this.lhs.apply(algebre.imply.equal.piecewise.invert, index=0)
    

if __name__ == '__main__':
    prove(__file__)
