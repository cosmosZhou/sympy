from sympy import *
from axiom.utility import prove, apply
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply(imply=True)
def apply(given, t, alpha):
    abs_x_y = axiom.is_positive(given)
    x_y = axiom.is_Norm(abs_x_y)
    x, y = axiom.is_Substract(x_y)
    
    assert x.shape == y.shape == t.shape
    assert alpha > 0
    
    x_quote = Symbol("x'", definition=(x + t * alpha) / (1 + alpha))
    y_quote = Symbol("y'", definition=(y + t * alpha) / (1 + alpha))
    return StrictLessThan(Norm(x_quote - y_quote), Norm(x - y))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,))
    y = Symbol.y(real=True, shape=(n,))
    t = Symbol.t(real=True, shape=(n,))
    
    alpha = Symbol.alpha(real=True, positive=True)
    Eq << apply(Norm(x - y) > 0, t, alpha)
    
    Eq << Eq[-1].this.lhs.arg.args[0].definition
    
    Eq << Eq[-1].this.lhs.arg.args[0].args[1].definition
    
    Eq << Eq[-1].this.lhs.arg.ratsimp()

    Eq << Eq[-1] * (1 + alpha)
    
    Eq << Eq[-1] - Eq[-1].lhs
    
    Eq << Eq[-1].this.rhs.collect(Norm(x - y)).reversed
    
    Eq << Eq[2] * alpha
    

if __name__ == '__main__':
    prove(__file__)

