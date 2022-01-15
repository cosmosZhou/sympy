from util import *


@apply
def apply(self):
    arg = self.of(Exp)
    if arg.is_Mul:
        [*args] = arg.args
        for i, block in enumerate(args):
            if block.is_BlockMatrix:
                break
        else:
            return
        del args[i]
        e = Mul(*args)
        args = block.args
        args = [exp(b * e) for b in args]
        axis = block.axis
    else:
        assert arg.is_BlockMatrix
        axis = arg.axis
        args = arg.args
        args = [exp(e) for e in args]
    return Equal(self, BlockMatrix[axis](args), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, n = Symbol(integer=True, positive=True)
    A = Symbol(real=True, shape=(a, n))
    B = Symbol(real=True, shape=(b, n))
    Eq << apply(exp(BlockMatrix(A, B)))

    i = Symbol(domain=Range(a + b))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.apply(algebra.exp.to.piece)





if __name__ == '__main__':
    run()
# created on 2021-12-19
