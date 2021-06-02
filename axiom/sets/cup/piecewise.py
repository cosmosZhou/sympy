from util import *




@apply
def apply(self):
    assert self.is_Cup
    f = self.function
    return Equal(self, self.func(Piecewise((f, self.limits_cond), (f.etype.emptySet, True)), *((x,) for x, *_ in self.limits)))


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(etype=dtype.real)

    Eq << apply(Cup[x:A, y:B](f(x, y)))

    Eq << Eq[0].this.rhs.function.apply(sets.piecewise.to.intersection)

    Eq << Equal(Cup[x](Eq[-1].rhs.function), Cup[x:A](f(x, y) & Eq[-1].rhs.function.args[1]), plausible=True)

    Eq << Eq[-1].this.lhs.apply(sets.cup.simplify.piecewise)

    Eq << sets.eq.imply.eq.cup.apply(Eq[-1], (y,))

    Eq << Eq[1].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.cup.to.union.st.piecewise)


if __name__ == '__main__':
    run()

