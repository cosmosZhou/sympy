from util import *


@apply
def apply(self):
    (fx, n), x, S[n] = self.of(Difference[Pow])
    assert not (fx - x)._has(x)
    return Equal(self, factorial(n))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    x = Symbol(real=True)
    k = Symbol(integer=True, nonnegative=True)
    t = x ** k
    assert t.is_complex
    assert t.is_extended_real
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Difference(x ** n, x, n))

    Eq.initial = Eq[0].subs(n, 0)

    Eq << Eq.initial.this.lhs.doit()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(discrete.difference.split, 1)

    Eq << Eq[-1].this.lhs.expr.doit()

    Eq << discrete.pow.to.sum.binom.Newton.apply((x + 1) ** (n + 1), swap=True) - x ** (n + 1)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum.to.add.pop_back)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.difference.to.sum)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.split, cond=n.set)

    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.mul)

    _k = Symbol('k', domain=Range(n))
    Eq.hypothesis_k = Eq[0].subs(n, _k)

    Eq << discrete.eq.imply.eq.difference.apply(Eq.hypothesis_k, (x, n - _k))

    Eq << Eq[-1].this.lhs.apply(discrete.difference.merge)

    Eq << Eq[-1] * binomial(n + 1, _k)

    Eq << Eq[-1].apply(algebra.eq.imply.eq.sum, (_k,))

    Eq << Eq[-1].this.lhs.limits_subs(_k, k)

    Eq << Eq[0] * (n + 1)

    Eq << Eq[-1] + Eq[-2]

    Eq << Infer(Eq[0] & Eq.hypothesis_k, Eq.induct, plausible=True)

    Eq << Eq[-1].this.lhs.args[0].apply(algebra.cond.given.all, _k)

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push_back)

    Eq << algebra.cond.infer.imply.cond.induct.second.split.all.apply(Eq.initial, Eq[-1], n=n)

    Eq << Eq[0].subs(n, _k)

    
    


if __name__ == '__main__':
    run()

# created on 2020-10-12
# updated on 2021-12-01