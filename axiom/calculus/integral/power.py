from axiom.utility import prove, apply
from sympy import *
from axiom import calculus, algebra


@apply
def apply(n, a=0, b=None, x=None):
    assert n.is_integer
    
    if x is None:
        x = Symbol.x(real=True)
    
    return Equal(Integral(x ** n, (x, a, b)), (b ** (n + 1) - a * (n + 1)) / (n + 1))


@prove
def prove(Eq): 

    x = Symbol.x(real=True)
    n = Symbol.n(integer=True, nonnegative=True)

    Eq << apply(n, b=x)
    
    f = Symbol.f(Eq[0].lhs)
    g = Symbol.g(Eq[0].rhs)

    Eq << diff(f, x).this.expr.definition
    
    Eq << Eq[-1].this.rhs.doit()
    
    Eq.df = Eq[-1].this.rhs.powsimp()
    
    Eq << diff(g, x).this.expr.definition

    Eq << Eq[-1].this.rhs.doit()
    
    Eq << Eq[-1].this.rhs.powsimp()
    
    Eq << Eq.df - Eq[-1]
    
    Eq << Eq[-1].this.lhs.apply(calculus.add.to.derivative)
    
    Eq << calculus.is_zero.imply.exists_eq.constant.apply(Eq[-1])
    
    Eq << Eq[-1].this.function.function.lhs.args[0].definition
    
    Eq << Eq[-1].this.find(-~Symbol).definition
    
    Eq << algebra.exists_forall.imply.exists_et.subs.apply(Eq[-1], x, 0)
    
    Eq << Eq[-1].this.function.function.args[1].lhs.doit()
    
    Eq << Eq[-1].this.function.function.apply(algebra.eq.eq.imply.eq.transit)
    
    Eq << Eq[-1].reversed
    
    
if __name__ == '__main__':
    prove()

