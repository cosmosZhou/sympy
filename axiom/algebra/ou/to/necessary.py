from util import *


@apply
def apply(self, index):
    [*eqs] = self.of(Or)
    p = eqs[index]
    if isinstance(index, slice):
        p = Or(*p)

    del eqs[index]
    q = Or(*eqs)

    return Equivalent(self, Necessary(q, p.invert()), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    B = Symbol.B(etype=dtype.integer)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Or(x <= y, f(x) > g(y), Contains(y, B)), index=slice(1, 3))

    Eq << Eq[-1].this.rhs.apply(algebra.necessary.to.ou)


if __name__ == '__main__':
    run()
