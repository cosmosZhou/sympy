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

    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    Eq << apply(Equal(Lamda[k:n](f(k)), Lamda[k:n](g(k))) & Equal(f(n), g(n)) & Contains(x, A), i=0, j=1)

    Eq << algebra.equivalent.given.et.apply(Eq[0])

    Eq <<= algebra.suffice_et.given.suffice.delete.apply(Eq[-2]), Eq[-1].this.rhs.args[0].apply(algebra.eq.imply.et.eq.blockmatrix, simplify=None)

    Eq << Eq[-1].this.lhs.apply(algebra.eq.eq.imply.eq.concatenate, simplify=None)


if __name__ == '__main__':
    run()
