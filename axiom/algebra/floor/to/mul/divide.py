from util import *
import axiom



@apply
def apply(self):
    div = self.of(Floor)
    n, d = axiom.is_Divide(div)

    return Equal(self, (n - n % d) / d)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(n // d)

    Eq << Eq[0].this.find(Mod).apply(algebra.mod.to.add)

if __name__ == '__main__':
    run()

