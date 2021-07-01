from util import *


@apply
def apply(self):    
    *args, x = self.of(Expr + Floor)
    rhs = Floor(x + Add(*args))
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(floor(n / d - S.One / 2) + 1)

    x = Symbol.x(Eq[0].find(Floor).arg)
    Eq << Eq[0].subs(x.this.definition.reversed)

    


if __name__ == '__main__':
    run()