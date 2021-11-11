from util import *


@apply
def apply(self):
    b, e = self.of(Abs[Pow])
    assert e.is_real
    return Equal(self, abs(b) ** e)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(complex=True, zero=False)
    Eq << apply(abs(x ** -1))

    Eq << algebra.expr.to.mul.expi.apply(x)

    Eq << Eq[0].subs(Eq[1])

    


if __name__ == '__main__':
    run()
# created on 2018-07-26
# updated on 2018-07-26
