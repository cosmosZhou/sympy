from util import *


@apply
def apply(self):
    n, d = self.of(Floor[Expr / Expr])
    return Equal(self, (n - n % d) / d)


@prove
def prove(Eq):
    from axiom import algebra
    n, d = Symbol(integer=True)
    Eq << apply(n // d)

    Eq << Eq[0].this.find(Mod).apply(algebra.mod.to.add)


if __name__ == '__main__':
    run()

# created on 2018-08-10
# updated on 2018-08-10
