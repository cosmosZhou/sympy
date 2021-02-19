from sympy import Symbol, Boole, Or, Times
from sympy.core.relational import Equality, StrictLessThan, Unequal, GreaterThan, \
    LessThan
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy.functions.elementary.piecewise import Piecewise

from sympy.core.function import Function
from axiom import algebre, sets
import axiom
from sympy.sets.sets import Interval
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(given, t, alpha, beta):
    abs_x_y = axiom.is_positive(given)
    x_y = axiom.is_Abs(abs_x_y)
    x, y = axiom.is_Substract(x_y)
    
    assert x.shape == y.shape == t.shape
    assert alpha > 0
    assert beta > 0
    
    x_quote = Symbol("x'", definition=(x + t * alpha) / (1 + alpha))
    y_quote = Symbol("y'", definition=(y + t * beta) / (1 + beta))
    return StrictLessThan(abs(x_quote - y_quote), abs(x - y))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,))
    y = Symbol.y(real=True, shape=(n,))
    
    x = Symbol.x(real=True, shape=())
    y = Symbol.y(real=True, shape=())    
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    lamda = Symbol.lamda(domain=Interval(0, 1))
    t = Symbol.t(definition=lamda * x + (1 - lamda) * y)
    
    alpha = Symbol.alpha(real=True, positive=True)
    beta = Symbol.beta(real=True, positive=True)
    Eq << apply(abs(x - y) > 0, t=t, alpha=alpha, beta=beta)
    
    Eq << Eq[-1].this.lhs.arg.args[0].definition
    
    Eq << Eq[-1].this.lhs.arg.args[0].args[1].definition
    
    Eq << Eq[-1].this.lhs.arg.ratsimp()

    Eq << Eq[-1] * (1 + alpha + beta + alpha * beta)
    
    Eq.less_than = algebre.imply.less_than.abs.substract.apply(Eq[-1].lhs.arg, x - y)
    
    Eq << Eq[0] * (alpha - beta)
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1] + (x * beta - y * alpha)
    
    Eq << Eq[-1].this.rhs.factor()
    
    Eq << algebre.equal.imply.equal.abs.apply(Eq[-1])
    
    Eq << Eq[-1].this.rhs.astype(Times)
    
    Eq << (alpha * lamda + (1 - lamda) * beta).this.expand()
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq[-1].this.lhs.arg.expand()
    
    Eq << Eq.less_than + Eq[-1]
    
    Eq.less_than = Eq[-1].this.rhs.collect(abs(x - y))
    
    Eq.strict_less_than = StrictLessThan(alpha * lamda + beta * (1 - lamda) + 1, alpha * beta + alpha + beta + 1, plausible=True)
    
    Eq << Eq.strict_less_than.this.lhs.expand()
    
    Eq << LessThan(alpha * lamda - beta * lamda, alpha * lamda, plausible=True)
    
    Eq << LessThan(lamda * alpha, alpha, plausible=True)
    
    Eq << Eq[-1] / alpha
    
    Eq << algebre.less_than.less_than.imply.less_than.transit.apply(Eq[-2], Eq[-1])
    
    Eq << StrictLessThan(0, alpha * beta, plausible=True)
    
    Eq << Eq[-1] + Eq[-2]
    
    Eq << algebre.is_positive.strict_less_than.imply.strict_less_than.multiply.apply(Eq[3], Eq.strict_less_than)
    
    Eq << algebre.less_than.strict_less_than.imply.strict_less_than.transit.apply(Eq.less_than, Eq[-1])    


if __name__ == '__main__':
    prove(__file__)

