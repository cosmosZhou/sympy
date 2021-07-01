from util import *


def absorb(Sum, self):
    (fx, (k, a, b)), fi = self.of(Sum.operator[Sum[Tuple], Basic])
    assert k.is_integer
    assert fx._subs(k, a - 1) == fi
    return Sum[k:a - 1:b](fx)

@apply
def apply(self):
    return Equal(self, absorb(Sum, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True)
    i = Symbol.i(domain=Range(0, n))
    f = Function.f(integer=True)
    Eq << apply(Add(Sum[k:1 + i:n](f(k)), f(i)))

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.split, cond={i})


if __name__ == '__main__':
    run()
