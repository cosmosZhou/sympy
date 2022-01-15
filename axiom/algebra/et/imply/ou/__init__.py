from util import *


@apply
def apply(self):
    for i, eq in enumerate(self.args):
        if isinstance(eq, Or):
            args = [*self.args]
            del args[i]
            this = self.func(*args)
            return Or(*((arg & this).simplify() for arg in eq.args))


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c, d = Symbol(integer=True, given=True)
    x, y = Symbol(real=True, given=True)
    f, g = Function(real=True)
    Eq << apply(And((a < b) | (c < d), (f(x) < g(y))))

    Eq << ~Eq[-1]

    Eq << algebra.et.imply.et.apply(Eq[0])

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[-1], Eq[-3], invert=True)

    Eq <<= Eq[-1] & Eq[-3]


if __name__ == '__main__':
    run()

from . import collect
# created on 2018-01-06
# updated on 2021-11-20
