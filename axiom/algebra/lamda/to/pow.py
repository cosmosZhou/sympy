from util import *


@apply
def apply(self):
    p, *limits = self.of(Lamda)
    if p.is_Mul:
        one, p = p.args
        assert one.is_OneMatrix
        base, exponent = p.of(Pow)
        base *= one
    else:
        base, exponent = p.of(Pow)
    assert not exponent.shape
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

    j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a, b = Symbol(real=True, shape=(n,))
    Eq << apply(Lamda[j:n](a[j] ** b[j]))

    _j = Symbol('j', domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], _j)

    
    


if __name__ == '__main__':
    run()
# created on 2019-10-19
# updated on 2021-12-19