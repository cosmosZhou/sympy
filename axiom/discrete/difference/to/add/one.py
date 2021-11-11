from util import *


@apply
def apply(self):
    [*args], variable, count = self.of(Difference[Add])

    assert count == 1
    rhs = Add(*(Difference(arg, variable, count).simplify() for arg in args))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    f, g = Function(real=True)
    x = Symbol(real=True)
    Eq << apply(Difference(f(x) + g(x), x))

    Eq << Eq[0].this.find(Difference).doit()

    Eq << Eq[-1].this.find(Difference).doit()
    Eq << Eq[-1].this.find(Difference).doit()




if __name__ == '__main__':
    run()
# created on 2020-10-08
# updated on 2020-10-08
