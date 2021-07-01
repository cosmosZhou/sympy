from util import *


@apply
def apply(self):
    x = self.of(Floor)
    return Equal(self, x - frac(x))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    Eq << apply(floor(x))

    Eq << Eq[-1].this.find(frac).apply(algebra.frac.to.add)

if __name__ == '__main__':
    run()

