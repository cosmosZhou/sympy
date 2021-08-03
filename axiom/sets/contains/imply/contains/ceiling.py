from util import *


@apply
def apply(contains):
    x, domain = contains.of(Contains)
    a, b = domain.of(Interval)
    assert domain.left_open and not domain.right_open
    if not b.is_integer:
        b = Ceiling(b)
    if not a.is_integer:
        a = Floor(a)    
    return Contains(Ceiling(x), Range(a + 1, b + 1))


@prove
def prove(Eq):
    from axiom import sets

    a, b = Symbol(real=True)
    x = Symbol(real=True)
    Eq << apply(Contains(x, Interval(a, b, left_open=True)))

    Eq << sets.contains.imply.contains.relax.interval.apply(Eq[0])

    
    

    

    Eq << Eq[-1].this.rhs.apply(sets.interval.to.cup)

    Eq << sets.contains.imply.any_contains.st.cup.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(sets.contains.imply.eq.ceiling)

    Eq << Eq[-1].this.expr.apply(sets.eq.imply.contains.finiteset)

    Eq << sets.any_contains.imply.contains.cup.apply(Eq[-1])

    i = Eq[-1].rhs.variable
    Eq << Eq[-1].this.rhs.limits_subs(i, i - 1)


if __name__ == '__main__':
    run()