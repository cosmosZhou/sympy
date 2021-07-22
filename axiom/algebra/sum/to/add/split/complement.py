from util import *


@apply
def apply(self):
    fx, (x, S) = self.of(Sum)
    A, B = S.of(Complement)
    return Equal(self, Sum[x:A](fx) - Sum[x:A & B](fx), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(integer=True)
    f = Function.f(real=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    Eq << apply(Sum[x:A - B](f(x)))

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.to.add.split, cond=B)

    

    

    

    

    

    


if __name__ == '__main__':
    run()