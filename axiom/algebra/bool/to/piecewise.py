from util import *


@apply
def apply(self):
    cond = self.of(Bool)
    return Equal(self, Piecewise((1, cond), (0, True)))


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(Bool(x > y))

    


if __name__ == '__main__':
    run()

