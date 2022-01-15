from util import *


@apply
def apply(self):
    args = self.of(Add)
    multiplicants = [arg.of(MatMul) for arg in args]

    i = 0
    while len({factor[i] for factor in multiplicants}) == 1:
        i += 1
    if i:
        lhs = MatMul(*multiplicants[0][:i])
        rhs = Add(*(MatMul(*factor[i:]) for factor in multiplicants))
    else:
        i = -1
        while len({factor[i] for factor in multiplicants}) == 1:
            i -= 1

        i += 1
        rhs = MatMul(*multiplicants[0][i:])
        lhs = Add(*(MatMul(*factor[:i]) for factor in multiplicants))

    return Equal(self, lhs @ rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    x, a, b = Symbol(shape=(n, n), complex=True)
    Eq << apply(x @ a + x @ b)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.add)





if __name__ == '__main__':
    run()
# created on 2021-12-26
