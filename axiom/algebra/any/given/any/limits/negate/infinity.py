from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Any)
    return Any[i](expr._subs(i, -i))


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Any[i](f(i) >= 0))

    Eq << algebra.any.imply.any.limits.negate.infinity.apply(Eq[-1])








if __name__ == '__main__':
    run()
# created on 2019-02-13
