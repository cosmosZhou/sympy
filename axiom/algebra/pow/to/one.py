from util import *


@apply
def apply(self):
    p = self.of(Pow[-1, Expr])
    n, *_ = p.free_symbols
    p = p.as_poly(n)
    assert p.degree() == 2
    c = p.nth(0)
    assert p.nth(2) == 1
    b = p.nth(1)
    t = (b - 1) / 2
    assert c == t ** 2 + t
    assert t.is_integer
    return Equal(self, 1)


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n, a = Symbol(integer=True)
    Eq << apply((-1) ** (n ** 2 + n * (2 * a + 1) + a ** 2 + a))

    t = Symbol(2 * binomial(n + a + 1, 2))
    Eq << t.this.definition

    Eq << algebra.eq.imply.eq.pow.apply(Eq[1], base=-1)

    Eq << Eq[1].this.find(Binomial).apply(discrete.binomial.to.mul.fallingFactorial.doit)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add, deep=True)

    Eq << Eq[2].subs(Eq[-1])

    Eq << Eq[0].this.find(Mul).apply(algebra.mul.to.add)


if __name__ == '__main__':
    run()
