from util import *


@apply
def apply(self, *, simplify=True):
    (ft, (t, a, b)), (x, _1) = self.of(Derivative[Integral])
    assert b._has(x) and not a._has(x)
    db = Derivative[x](b)
    if simplify:
        db = db.simplify()
    assert ft.is_continuous(t)
    assert b.is_continuous(x)

    return Equal(self, ft._subs(t, b) * db)


@prove(proved=False)
def prove(Eq):
    from axiom import calculus, algebra

    x, t, a = Symbol(real=True)
    f, h = Function(real=True, continuous=True)
    Eq << apply(Derivative[x](Integral[t:a:h(x)](f(t))))

    Eq << Eq[0].this.lhs.apply(calculus.derivative.to.limit)

    epsilon = Eq[-1].lhs.variable
    Eq << Eq[-1].this.find(Add).apply(calculus.add.to.integral.connect)

    Eq << calculus.imply.is_continuous.interval.apply(*Eq[-1].find(Integral).args)

    Eq << calculus.is_continuous.imply.any_eq.interval01.mean_value_theorem.apply(Eq[-1], 'lamda')

    Eq << Eq[-1].this.expr.apply(calculus.eq.imply.eq.limit.div, epsilon)

    lamda = Eq[-1].variable
    Eq <<= Limit[epsilon:0](Eq[-1].find(h)).this.apply(calculus.limit.to.expr.continuity), Limit[epsilon:0](Eq[-1].find(h[Add])).this.apply(calculus.limit.to.expr.continuity)

    Eq <<= Eq[-1] * lamda, Eq[-1] * (1 - lamda)

    Eq <<= Eq[-2].this.lhs.apply(calculus.mul.to.limit), Eq[-1].this.lhs.apply(calculus.mul.to.limit)

    Eq << calculus.eq_limit.eq_limit.imply.eq_limit.add.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)


if __name__ == '__main__':
    run()
# created on 2020-05-05
