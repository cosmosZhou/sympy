from util import *


@apply
def apply(self, old, new):
    expr, (i, a, b) = self.of(Cup)
    assert old == i
    c = new + i + 1
    #new = c - i - 1
    assert not c._has(i)
    #i = a => new = c - a - 1
    #i = b - 1 => new = c - (b - 1) - 1 = c - b
    return Equal(self, Cup[i:c - b: c - a](expr._subs(old, new)), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets

    i = Symbol.i(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    c = Symbol.c(integer=True)
    f = Function.f(etype=dtype.real)
    Eq << apply(Cup[i:a:b](f(i)), i, c - i)

    Eq << Eq[-1].this.rhs.apply(sets.cup.piecewise)

    Eq << Eq[-1].this.rhs.apply(sets.cup.limits.negate.infinity)

    Eq << Eq[-1].this.rhs.find(Contains).apply(sets.contains.negate)

    Eq << Eq[-1].this.rhs.limits_subs(i, i - c)

    

    


if __name__ == '__main__':
    run()