from util import *


@apply(given=None)
def apply(self):
    for i, eq in enumerate(self.args):
        if isinstance(eq, Or):
            break
    else:
        return
    
    args = [*self.args]
    del args[i]
    this = self.func(*args)
    return Equivalent(self, Or(*((arg & this).simplify() for arg in eq.args)))


@prove
def prove(Eq):
    from axiom import algebra
    a, b, c, d = Symbol(integer=True, given=True)


    x, y = Symbol(real=True, given=True)

    f, g = Function(real=True)

    Eq << apply(And((a < b) | (c < d), (f(x) < g(y))))

    Eq << algebra.iff.given.et.apply(Eq[-1])

#     Eq << Eq[-2].this.lhs.apply(algebra.et.imply.ou, simplify=False)

    Eq << Eq[-1].this.rhs.apply(algebra.ou.imply.et.collect, cond=f(x) < g(y), simplify=False)


if __name__ == '__main__':
    run()

# created on 2018-01-21
from . import collect
