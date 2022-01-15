from util import *


def of_set_comprehension(self):
    ak, (k, b) = self.of(Cup[FiniteSet, Tuple[0, Expr]])
    return Lamda[k:b](ak).simplify()


@apply
def apply(imply):
    lhs, rhs = imply.of(Equal)
    a = of_set_comprehension(lhs)
    b = of_set_comprehension(rhs)
    k = lhs.variable
    return Equal(a[k], b[k])


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True, positive=True)
    a, b = Symbol(integer=True, shape=(n,))

    Eq << apply(Equal(a.set_comprehension(), b.set_comprehension()))

    i = Eq[0].lhs.variable

    Eq << sets.eq.imply.eq.set_comprehension.apply(Eq[-1], (i, 0, n), simplify=None)


if __name__ == '__main__':
    run()

# created on 2021-03-29
