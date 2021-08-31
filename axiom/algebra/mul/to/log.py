from util import *


@apply
def apply(self):
    *t, x = self.of(Expr * Log)
    t = Mul(*t)
    rhs = log(x ** t)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    t = Symbol(real=True)
    x = Symbol(real=True, positive=True)
    Eq << apply(t * log(x))

    Eq << algebra.eq.given.eq.exp.apply(Eq[0])

    y = Symbol(log(x))
    Eq << y.this.definition

    Eq <<= Eq[-1] * t, algebra.eq.imply.eq.exp.apply(Eq[-1])

    Eq <<= algebra.eq.imply.eq.exp.apply(Eq[-2]), algebra.eq.imply.eq.pow.apply(Eq[-1], exp=t)
    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
