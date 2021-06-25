from util import *


def convert(self):
    base, *indices = self.of(Slice)
    if len(indices) == 1:
        start, stop = self.index
        size = stop - start
        assert size.is_Integer

        array = []
        for i in range(size):
            array.append(self[i])

        return Matrix(tuple(array))
    elif len(indices) == 2:
        for index in indices:
            start, stop = index
    else:
        return

    
@apply
def apply(self):
    rhs = convert(self)
    
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = 4
    a = Symbol.a(real=True, shape=(oo,))

    Eq << apply(a[i:i + 4])

    Eq << Equal(a[i:i + 4], Lamda[j:4](a[i + j]), plausible=True)

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.matrix)


if __name__ == '__main__':
    run()

