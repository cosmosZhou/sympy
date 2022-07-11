from util import *


@apply
def apply(self):
    x, n = self.of(Expr ** Expr)
    assert n.is_integer
    return Equal(self, (-1) ** n * (-x) ** n)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply((x - y) ** 3)

    Eq << Eq[-1].this.lhs.apply(algebra.pow.to.add)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.pow.to.add)

    
    


if __name__ == '__main__':
    run()
# created on 2018-11-14
# updated on 2022-07-08
