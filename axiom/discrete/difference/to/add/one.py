from util import *


@apply
def apply(self):
    [*args], variable, count = self.of(Difference[Add])
    
    assert count == 1
    rhs = Add(*(Difference(arg, variable, count).simplify() for arg in args))
        
    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    f = Function.f(real=True)
    g = Function.g(real=True)
    x = Symbol.x(real=True)
    Eq << apply(Difference(f(x) + g(x), x))

    Eq << Eq[0].this.find(Difference).doit()

    Eq << Eq[-1].this.find(Difference).doit()
    Eq << Eq[-1].this.find(Difference).doit()

    


if __name__ == '__main__':
    run()