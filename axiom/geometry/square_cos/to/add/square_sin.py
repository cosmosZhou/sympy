from util import *


@apply
def apply(self):
    x = self.of(Cos ** 2)
    return Equal(self, 1 - sin(x) ** 2)


@prove
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(cos(x) ** 2)

    Eq << Eq[-1] - Eq[-1].rhs.args[1]

    Eq << Eq[-1].this.lhs.trigsimp()

    #https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F


if __name__ == '__main__':
    run()
# created on 2020-06-30
