from util import *


@apply
def apply(self):
    (function, *limits), variable, count = self.of(Difference[Sum])
    
    assert count == 1
    rhs = Sum(Difference(function, variable, count).simplify(), *limits)
        
    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    from axiom import algebra

    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(real=True)
    x = Symbol.x(real=True)
    Eq << apply(Difference(Sum[i:n](f[i](x)), x))

    Eq << Eq[0].this.lhs.doit()

    Eq << Eq[-1].this.rhs.function.doit()
    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)


if __name__ == '__main__':
    run()