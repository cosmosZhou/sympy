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

    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    A = Symbol.A(real=True, shape=(m, n))
    B = Symbol.B(real=True, shape=(m, n))
    C = Symbol.C(real=True, shape=(m, n))
    D = Symbol.D(real=True, shape=(m, n))
    Eq << apply(Add(BlockMatrix(A, B), BlockMatrix(C, D)))

    i = Symbol.i(domain=Range(0, m * 2))
    j = Symbol.j(domain=Range(0, n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)
    Eq << Eq[-1].this.lhs.apply(algebra.add.to.piecewise.st.two_pieces)


if __name__ == '__main__':
    run()