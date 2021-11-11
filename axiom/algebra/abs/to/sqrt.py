from util import *


@apply
def apply(self):
    z = self.of(Abs)
    x = Re(z)
    y = Im(z)
    return Equal(self, sqrt(x * x + y * y))


@prove
def prove(Eq):
    from axiom import algebra
    z = Symbol(complex=True)
    Eq << apply(abs(z))
    Eq << Eq[0].this.lhs.arg.apply(algebra.expr.to.add.complex)


if __name__ == '__main__':
    run()
    
# created on 2018-06-12
# updated on 2018-06-12
