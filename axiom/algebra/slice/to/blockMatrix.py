from util import *


@apply
def apply(self):
    i_shape, *shape = self.shape
    assert shape
    assert isinstance(i_shape, int) or i_shape.is_Number
    array = []
    for i in range(i_shape):
        array.append(self[sympify(i)])
    rhs = BlockMatrix(*array)
    
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True, shape=(oo, n))
    Eq << apply(a[i:i + 4])

    Eq << Equal(a[i:i + 4], Lamda[j:4](a[i + j]), plausible=True)

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.blockMatrix)


if __name__ == '__main__':
    run()