from util import *



@apply(given=None)
def apply(self):
    expr = self.of(Unequal[0])
    n, two = expr.of(Mod)
    assert two == 2
    return Equivalent(self, Equal(expr, 1))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True)

    Eq << apply(Unequal(n % 2, 0))

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.mod_is_nonzero.imply.is_odd)

    Eq << Eq[-1].this.rhs.apply(algebra.is_nonzero.given.is_odd)

if __name__ == '__main__':
    run()
