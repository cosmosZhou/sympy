from util import *
import axiom



@apply(given=None)
def apply(self):
    for i, eq in enumerate(self.args):
        if isinstance(eq, Or):
            args = [*self.args]
            del args[i]
            this = self.func(*args)
            return Equivalent(self, Or(*((arg & this).simplify() for arg in eq.args)))


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)

    c = Symbol.c(integer=True, given=True)
    d = Symbol.d(integer=True, given=True)

    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    f = Function.f(real=True)
    g = Function.g(real=True)

    Eq << apply(And((a < b) | (c < d), (f(x) < g(y))))

    Eq << algebra.equivalent.given.cond.apply(Eq[-1])

#     Eq << Eq[-2].this.lhs.apply(algebra.et.imply.ou, simplify=False)

    Eq << Eq[-1].this.rhs.apply(algebra.ou.imply.et.collect, cond=f(x) < g(y), simplify=False)


if __name__ == '__main__':
    run()

