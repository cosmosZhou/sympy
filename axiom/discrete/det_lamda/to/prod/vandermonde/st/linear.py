from util import *


@apply
def apply(self):
    (delta, i), (j, S[0], n), (S[i], S[0], S[n]) = self.of(Det[Lamda[Pow]])
    delta -= j
    assert not delta._has(j)
    
    return Equal(self, Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(domain=Range(2, oo), given=False)
    i, j = Symbol(integer=True)
    delta = Symbol(real=True)
    Eq << apply(Det(Lamda[j:n, i:n]((j + delta) ** i)))

    Eq << discrete.prod.to.factorial.apply(Product[j:i](i - j))

    Eq << algebra.eq.imply.eq.prod.apply(Eq[-1], (i, 0, n))

    a = Symbol(Lamda[j:n](j + delta))
    Eq << a[j].this.definition

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.apply(discrete.det_lamda.to.prod.vandermonde)

    Eq << Eq[-1].this.find(Indexed).definition

    Eq << Eq[-1].this.find(Indexed).definition


if __name__ == '__main__':
    run()
# created on 2022-01-15
