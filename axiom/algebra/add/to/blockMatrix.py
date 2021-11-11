from util import *


@apply
def apply(self, evaluate=False):
    args = self.of(Add)
    size = None

    blocks = []
    for block in args:
        args = block.of(BlockMatrix)
        if size is None:
            size = len(args)
        else:
            assert size == len(args)
        blocks.append(args)

    args = []
    for i in range(size):
        args.append(Add(*(block[i] for block in blocks)))

    rhs = BlockMatrix(*args)

    return Equal(self, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    n, m = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(real=True, shape=(m, n))
    Eq << apply(Add(BlockMatrix(A, B), BlockMatrix(C, D)))

    i = Symbol(domain=Range(m * 2))
    j = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)
    Eq << Eq[-1].this.lhs.apply(algebra.add.to.piece.st.two_pieces)


if __name__ == '__main__':
    run()
# created on 2018-08-04
# updated on 2018-08-04
