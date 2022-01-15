from util import *


@apply
def apply(self):
    [*args] = self.of(Add)
    for i, block in enumerate(args):
        if block.is_BlockMatrix:
            break
    else:
        return
    
    del args[i]
    coeff = Add(*args)    
    rhs = BlockMatrix[block.axis]([arg + coeff for arg in block.args])
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    n, m = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(real=True, shape=(m, n))
    x = Symbol(real=True, shape=(n,))
    Eq << apply(Add(BlockMatrix(A, B), x))

    i = Symbol(domain=Range(m * 2))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.piece)

    


if __name__ == '__main__':
    run()
# created on 2022-01-14
