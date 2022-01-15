from util import *


@apply
def apply(self):
    blocks = []
    size = None
    axis = self.axis
    for block in self.of(BlockMatrix):
        args = block.of(Add)
        if size is None:
            size = len(args)
        else:
            assert size == len(args)

        blocks.append(args)

    args = []
    for i in range(size):
        additives = [block[i] for block in blocks]

        shapes = [a.shape[:axis] + a.shape[axis + 1:] for a in additives]
        assert len({*shapes}) == 1

        args.append(BlockMatrix[axis](additives))

    return Equal(self, Add(*args), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    n, m = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(real=True, shape=(m, n))
    Eq << apply(BlockMatrix(A + C, B + D))

    Eq << Eq[0].this.rhs.apply(algebra.add_block.to.block)


if __name__ == '__main__':
    run()
# created on 2021-12-30
