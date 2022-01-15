from util import *


@apply
def apply(self):
    args = self.of(Mul)

    limits = None
    factors = []
    for lamda in args:
        f, *_limits = lamda.of(Lamda)
        if limits is None:
            limits = _limits
        else:
            assert limits == _limits            

        factors.append(f)
    return Equal(self, Lamda(Mul(*factors), *limits))

@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(integer=True)
    Eq << apply(Lamda[k:n](f(k)) * Lamda[k:n](g(k)))

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)





if __name__ == '__main__':
    run()
# created on 2021-12-16
