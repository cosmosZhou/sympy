from util import *


@apply
def apply(self):
    x, y = self.of(KroneckerDelta)
    return Equal(self, Piecewise((1, Equal(x, y)), (0, True)))


@prove(provable=False)
def prove(Eq):
    x, y = Symbol(integer=True)
    Eq << apply(KroneckerDelta(x, y))




if __name__ == '__main__':
    run()
