from util import *



@apply(given=None)
def apply(self):
    for i, eq in enumerate(self.args):
        if isinstance(eq, And):
            args = [*self.args]
            del args[i]
            this = self.func(*args)
            return Equivalent(self, And(*((arg | this).simplify() for arg in eq.args)))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    f, g = Function(real=True)
    Eq << apply(Or(Unequal(x, y) & (y > 0), Equal(f(x), g(y))))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ou.imply.et)

    Eq << Eq[-1].this.lhs.apply(algebra.ou.given.et)


if __name__ == '__main__':
    run()

# created on 2020-02-21
