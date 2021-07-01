from util import *

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply
def apply(a, wrt=None):
    if wrt is None:
        wrt = a.generate_var(**a.type.dict)
    U = a.universalSet
    return Equal(conditionset(wrt, Unequal(wrt, a)), U - a.set)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))

    Eq << apply(x)

    A = Symbol.A(Eq[0].lhs)
    B = Symbol.B(Eq[0].rhs)

    a = Eq[0].lhs.variable
    Eq.all_contains_in_B = All[a:A](Contains(a, B), plausible=True)

    Eq << Eq.all_contains_in_B.this.limits[0][1].definition

    Eq << Eq[-1].this.function.rhs.definition

    Eq.all_contains_in_A = All[a:B](Contains(a, A), plausible=True)

    Eq << Eq.all_contains_in_A.this.limits[0][1].definition

    Eq << Eq[-1].this.function.rhs.definition

    Eq << All[a:Eq[-1].function.invert()](Eq[-1].limits_cond.invert(), plausible=True)

    Eq << Eq[-1].this.function.simplify()

    Eq << algebra.all.imply.all.limits.invert.apply(Eq[-1])

    Eq << sets.all_contains.all_contains.imply.eq.apply(Eq.all_contains_in_A, Eq.all_contains_in_B)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

