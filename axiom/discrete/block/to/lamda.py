from util import *


@apply
def apply(self):
    shape = self.shape
    len_shape = len(shape)
    k = self.generate_var(integer=True)

    assert self.axis == 0

    rows = 0
    args = []
    for X in self.of(BlockMatrix):
        index = rows
        if len(X.shape) < len_shape:
            rows += 1
        else:
            rows += X.shape[0]

        if len(X.shape) == len_shape:
            args.append([X[k - index], k < rows])

    args[-1][1] = True
    return Equal(self, Lamda[k:rows](Piecewise(*args)))


@prove
def prove(Eq):
    from axiom import algebra

    n0, n1, n2, n3, m = Symbol(positive=True, integer=True, given=False)
    X0 = Symbol(shape=(n0, m), real=True)
    X1 = Symbol(shape=(n1, m), real=True)
    X2 = Symbol(shape=(n2, m), real=True)
    X3 = Symbol(shape=(n3, m), real=True)
    Eq << apply(BlockMatrix([X0, X1, X2, X3]))

    i = Symbol(domain=Range(n0 + n1 + n2 + n3))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)





if __name__ == '__main__':
    run()
# created on 2021-10-04
