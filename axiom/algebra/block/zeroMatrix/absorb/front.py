from util import *


@apply
def apply(self, index=-1):
    print('use BlockMatrix.subs instead, which is more flexible')
    args = self.of(BlockMatrix)
    if index < 0:
        index += len(args)

    zeroMatrix = args[index]
    assert zeroMatrix.is_ZeroMatrix
    [n] = zeroMatrix.shape
    front = args[index - 1]
    assert front == 0
    args = args[:index - 1] + (ZeroMatrix(n + 1),) + args[index + 1:]

    return Equal(self, BlockMatrix(args))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(integer=True)
    Eq << apply(BlockMatrix([x, 0, ZeroMatrix(n)]))

    i = Symbol(domain=Range(n + 2))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    
    


if __name__ == '__main__':
    run()
# created on 2021-11-21
# updated on 2021-11-22