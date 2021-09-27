from util import *


@apply
def apply(self):
    x, y = self.of(Cos[Add])
    return Equal(cos(x - y), cos(x) * cos(y) + sin(x) * sin(y))


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(real=True)
    Eq << apply(cos(x - y))

    Eq << Eq[-1].this.lhs.apply(geometry.cos.to.add.principle.add)

    #https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F


if __name__ == '__main__':
    run()
