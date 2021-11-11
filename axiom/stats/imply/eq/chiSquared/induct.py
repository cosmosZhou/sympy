from util import *


@apply
def apply(_Y, Y):
    X_squared_Sum = _Y.definition

    X_squared_Sum, [k] = X_squared_Sum.of(Lamda)

    function, (i, _k) = X_squared_Sum.of(Sum[Tuple[0, Expr]])
    assert _k == k

    X = pspace(X_squared_Sum).value.base

    y = pspace(Y).symbol
    assert y >= 0
    assert not y.is_random

    assert k == Y.distribution.of(ChiSquaredDistribution)

    assert function == X[i] * X[i]

    return Equal(Probability(Equal(_Y[k], y)), Probability(Equal(Y, y)).doit())


@prove
def prove(Eq):
    from axiom import calculus, algebra

    i = Symbol(integer=True, nonnegative=True)
    X = Symbol(shape=(oo,), distribution=NormalDistribution(0, 1))
    k = Symbol(integer=True, positive=True, given=False)
    Y = Symbol(distribution=ChiSquaredDistribution(k))
    _Y = Symbol.Y(Lamda[k](Sum[i:k](X[i] * X[i])))
    Eq << apply(_Y, Y)

    Eq.induct = Eq[-1].subs(k, k + 1)

    Eq << Eq[0].subs(k, k + 1) - Eq[0] + _Y[k]

    Eq.x_squared_y = Eq.induct.subs(Eq[-1])

    Eq << Eq.x_squared_y.lhs.this.doit(evaluate=False)

    Eq << Eq[-1].this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.find(~Probability * DiracDelta).doit()

    Eq << Eq[-1].this.rhs.find(Integral, Integral).doit()

    (_y, *_), *_ = Eq[-1].rhs.args[-1].limits
    y = Eq[1].lhs.arg.rhs
    Eq.hypothesis_k = Eq[1].subs(y, _y)

    Eq << Eq.hypothesis_k.this.lhs.args[0].args[0].definition

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    t = Symbol(domain=Interval(0, pi / 2))
    Eq << Eq[-1].this.rhs.args[-1].limits_subs(_y, y * sin(t) ** 2)

    Eq << Eq[-1].this.rhs.args[-1].expr.powsimp()

    Eq << calculus.trigonometry.wallis.beta.apply(1, k)

    x = Eq[-1].lhs.variable
    t = Eq[-2].rhs.args[-1].variable
    Eq << Eq[-1].this.lhs.limits_subs(x, t)

    #expand the BETA function into gamma function
    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.powsimp()

    Eq.initial = Eq[1].subs(k, 1)

    Eq << Eq[0].subs(k, 1).doit(deep=False)

    Eq << Eq.initial.subs(Eq[-1])

    Eq << Eq[-1].lhs.this.doit(evaluate=False)

    Eq << Infer(Eq[1], Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], n=k, start=1)

    #https://www.asmeurer.com/blog/


if __name__ == '__main__':
    run()
# created on 2021-07-17
# updated on 2021-07-17
