from util import *


@apply(given=None)
def apply(self):
    expr, (i,) = self.of(Any)
    return Equivalent(self, Any[i](expr._subs(i, -i)), evaluate=False)


@prove(proved=False)
def prove(Eq):
    from axiom import algebra

    i = Symbol.i(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    c = Symbol.c(integer=True)
    f = Function.f(real=True)
    Eq << apply(Any[i](f(i) >= 0))

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.any.imply.any.limits.negate.infinity)

    Eq << Eq[-1].this.lhs.apply(algebra.any.imply.any.limits.negate.infinity)


if __name__ == '__main__':
    run()