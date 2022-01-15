from util import *


@apply
def apply(self):
    for i, block in enumerate(self.args):
        if isinstance(block, BlockMatrix):
            break
    else:
        return
    
    args = [*self.args]
    args[i] = 1
    factor = Mul(*args)
    assert not factor.shape
    block = [b * factor for b in block.args]
    return Equal(self, BlockMatrix(block))


@prove
def prove(Eq):
    from axiom import algebra

    m, n = Symbol(integer=True, positive=True)
    A, B = Symbol(real=True, shape=(m, n))
    x = Symbol(real=True, shape=(n,))
    i = Symbol(integer=True)
    Eq << apply(BlockMatrix(A, B) * x[i])

    j = Symbol(domain=Range(m * 2))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], j)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.to.mul)


if __name__ == '__main__':
    run()
# created on 2021-12-30
