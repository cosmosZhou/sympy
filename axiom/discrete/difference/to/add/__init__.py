from util import *


@apply
def apply(self):
    [*args], *variable_count = self.of(Difference[Add])
    
    rhs = Add(*(Difference(arg, *variable_count).simplify() for arg in args))
        
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    f = Function.f(real=True)
    g = Function.g(real=True)
    x = Symbol.x(real=True)
    d = Symbol.d(integer=True, positive=True, given=False)
    Eq << apply(Difference(f(x) + g(x), x, d))

    Eq.initial = Eq[0].subs(d, 1)

    Eq << Eq.initial.this.lhs.apply(discrete.difference.to.add.one)

    Eq.induct = Eq[0].subs(d, d + 1)

    Eq << discrete.eq.imply.eq.difference.apply(Eq[0], (x, 1))

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.apply(discrete.difference.to.add.one)

    Eq << Eq.induct.induct()

    Eq << algebra.eq.suffice.imply.eq.induct.apply(Eq.initial, Eq[-1], n=d, start=1)


if __name__ == '__main__':
    run()

from . import one
