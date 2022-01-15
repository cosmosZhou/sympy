from util import *


@apply(given=None)
def apply(self, i=None, j=None):
    [*eqs] = self.of(And)

    eq_historic = eqs[i]
    eq_n = eqs[j]

    del eqs[i]
    eqs.remove(eq_n)

    lhs, rhs = eq_historic.of(Equal)
    n = lhs.shape[0]

    if lhs.is_Lamda and rhs.is_Lamda and lhs.variable == rhs.variable:
        k = rhs.variable
    else:
        k = eq_historic.generate_var(integer=True)

    fx = lhs[k]
    gy = rhs[k]

    _lhs, _rhs = eq_n.of(Equal)

    assert fx._subs(k, n) == _lhs
    assert gy._subs(k, n) == _rhs

    rhs = And(*eqs, Equal(Lamda[k:n + 1](fx).simplify(), Lamda[k:n + 1](gy).simplify()))
    return Equivalent(self, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f, g = Function(real=True)
    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    Eq << apply(Equal(Lamda[k:n](f(k)), Lamda[k:n](g(k))) & Equal(f(n), g(n)) & Element(x, A), i=0, j=1)

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq <<= algebra.infer_et.given.infer.delete.apply(Eq[-2]), Eq[-1].this.rhs.args[0].apply(algebra.eq.imply.et.eq.block, simplify=None)

    Eq << Eq[-1].this.lhs.apply(algebra.eq.eq.imply.eq.concatenate, simplify=None)


if __name__ == '__main__':
    run()
# created on 2019-05-01
