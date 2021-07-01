from util import *


@apply
def apply(self):    
    (expr, _x, d), x, n = self.of(Difference[Difference])
    assert x == _x    
    return Equal(self, Difference(expr, x, n + d), evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(real=True)
    d = Symbol.d(integer=True, positive=True, given=False)
    n = Symbol.n(integer=True, positive=True, given=False)
    Eq << apply(Difference(Difference(f(x), x, d), x, n - d))

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()