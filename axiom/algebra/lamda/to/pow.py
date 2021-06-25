from util import *


@apply
def apply(self):
    (base, exponent), *limits = self.of(Lamda[Pow])
    variables = [v for v, *_ in limits]
    if exponent.has(*variables):
        if base.has(*variables):
            rhs = Pow(Lamda(base, *limits).simplify(), Lamda(exponent, *limits).simplify())
        else:
            rhs = Pow(base, Lamda(exponent, *limits))
    else:
        rhs = Pow(Lamda(base, *limits), exponent)


    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True, shape=(n,))
    b = Symbol.b(real=True, shape=(n,))
    Eq << apply(Lamda[j:n](a[j] ** b[j]))

    _j = Symbol.j(domain=Range(0, n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], _j)


if __name__ == '__main__':
    run()