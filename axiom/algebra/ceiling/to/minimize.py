from util import *


@apply
def apply(self):
    x = self.of(Ceiling)
    n = x.generate_var(integer=True, var='n')
    return Equal(self, Minimize[n:n>=x](n))


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(Ceiling(x))

    #Eq << Eq[0].reversed + 1 - Floor(x)
    #Eq << Eq[-1].this.lhs.apply(algebra.add.to.frac)


if __name__ == '__main__':
    run()

