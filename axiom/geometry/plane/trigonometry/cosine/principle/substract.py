from util import *


@apply
def apply(x, y):
    return Equal(cos(x - y), cos(x) * cos(y) + sin(x) * sin(y))


@prove
def prove(Eq):
    from axiom import geometry
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(x, y)

    Eq << geometry.plane.trigonometry.cosine.principle.add.apply(x, -y)


# https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F
if __name__ == '__main__':
    run()
