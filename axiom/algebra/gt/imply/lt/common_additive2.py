from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(given, t, alpha, beta):
    abs_x_y = axiom.is_positive(given)
    x_y = axiom.is_Abs(abs_x_y)
    x, y = axiom.is_Substract(x_y)
    
    assert x.shape == y.shape == t.shape
    assert alpha > 0
    assert beta > 0
    
    x_quote = Symbol("x'", (x + t * alpha) / (1 + alpha))
    y_quote = Symbol("y'", (y + t * beta) / (1 + beta))
    return Less(abs(x_quote - y_quote), abs(x - y))


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
    t = Symbol.t(lamda * x + (1 - lamda) * y)
    
    alpha = Symbol.alpha(real=True, positive=True)
    beta = Symbol.beta(real=True, positive=True)
    Eq << apply(abs(x - y) > 0, t=t, alpha=alpha, beta=beta)
    
    Eq << Eq[-1].this.lhs.arg.args[0].definition
    
    Eq << Eq[-1].this.lhs.arg.args[0].args[1].definition
    
    Eq << Eq[-1].this.lhs.arg.ratsimp()

    Eq << Eq[-1] * (1 + alpha + beta + alpha * beta)
    
    Eq.less_than = algebra.imply.le.abs.substract.apply(Eq[-1].lhs.arg, x - y)
    
    Eq << Eq[0] * (alpha - beta)
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1] + (x * beta - y * alpha)
    
    Eq << Eq[-1].this.rhs.factor()
    
    Eq << algebra.eq.imply.eq.abs.apply(Eq[-1])
    
    Eq << Eq[-1].this.rhs.astype(Mul)
    
    Eq << (alpha * lamda + (1 - lamda) * beta).this.expand()
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq[-1].this.lhs.arg.expand()
    
    Eq << Eq.less_than + Eq[-1]
    
    Eq << Eq[-1].this.apply(algebra.le.simplify.terms.common)
    
    Eq.less_than = Eq[-1].this.rhs.collect(abs(x - y))
    
    Eq.lt = Less(alpha * lamda + beta * (1 - lamda) + 1, alpha * beta + alpha + beta + 1, plausible=True)
    
    Eq << Eq.lt.this.lhs.expand()
    
    Eq << LessEqual(alpha * lamda - beta * lamda, alpha * lamda, plausible=True)
    
    Eq << LessEqual(lamda * alpha, alpha, plausible=True)
    
    Eq << Eq[-1] / alpha
    
    Eq << algebra.le.le.imply.le.transit.apply(Eq[-2], Eq[-1])
    
    Eq << Less(0, alpha * beta, plausible=True)
    
    Eq << algebra.le.lt.imply.lt.add.apply(Eq[-2], Eq[-1])
    
    Eq << algebra.is_positive.lt.imply.lt.mul.apply(Eq[3], Eq.lt)
    
    Eq << algebra.le.lt.imply.lt.transit.apply(Eq.less_than, Eq[-1])    


if __name__ == '__main__':
    prove()

