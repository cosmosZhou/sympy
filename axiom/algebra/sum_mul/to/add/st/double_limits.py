from util import *


@apply
def apply(self):
    (xi, xj), (j, _0, i), (i, __0, n) = self.of(Sum[Mul])
    assert 0 == _0 == __0
    if not xi._has(i):
        xi, xj = xj, xi
    assert xj._subs(j, i) == xi
    return Equal(self, Sum[i:n](xi) ** 2 / 2 - Sum[i:n](xi ** 2) / 2)


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(Sum[j:i, i:n](x[i] * x[j]))

    Eq << algebra.square.to.add.st.sum.apply(Eq[0].find(Pow[Sum]))

    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()
