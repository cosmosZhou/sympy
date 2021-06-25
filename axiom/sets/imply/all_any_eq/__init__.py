from util import *


@apply
def apply(n, **kwargs):
    if 'etype' in kwargs:
        etype = kwargs['etype']
        if 'elements' in kwargs:
            S = n.generate_var(etype=etype, excludes=kwargs['elements'].free_symbols)
        else:
            S = n.generate_var(etype=etype)
    else:
        S = kwargs['set']
        etype = S.etype

    i = n.generate_var(integer=True)
    j = S.generate_var(integer=True, excludes={i})

    if 'elements' in kwargs:
        x = kwargs['elements']
    else:
        kwargs = etype.dict
        if 'shape' in kwargs:
            shape = (oo,) + kwargs['shape']
        else:
            shape = (oo,)
        kwargs.pop('shape')

        x = S.generate_var(shape=shape, **kwargs)

    return All[S:Equal(abs(S), n)](Any[x[:n]:All[j:i, i:n](Unequal(x[i], x[j]))](Equal(S, Cup[i:n]({x[i]}))))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol.n(domain=Range(2, oo), given=False)
    k = Symbol.k(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer * k)
    Eq << apply(n, set=S)

    Eq.initial = Eq[0].subs(n, 2)

    Eq << Eq.initial.this.function.doit(deep=True)
    
    Eq << Eq[-1].this.find(Slice).apply(algebra.slice.to.blockMatrix)

    Eq << Eq[-1].this.function.limits[0][1].reversed

    Eq << sets.imply.all_any_eq.two.apply(*Eq[-1].rhs.args, set=Eq[-1].variable)

    Eq.induct = Eq[0].subs(n, n + 1)

    A = Eq.induct.function.variable.base
    Eq << algebra.imply.all.limits_assert.apply(Eq.induct.limits)

    Eq.size_deduction = Eq[-1].this.function.apply(sets.eq.imply.any_eq.size_deduction, var=A[n])

    Eq << algebra.all.imply.ou.subs.apply(Eq[0], Eq.size_deduction.variable, Eq.size_deduction.lhs.arg)

    Eq << algebra.ou.imply.any_ou.apply(Eq[-1])

    Eq << algebra.cond.all.imply.all_et.apply(Eq[-1], Eq.size_deduction)

    Eq << Eq[-1].this.function.apply(algebra.any.any.imply.any_et)

    Eq << Eq[-1].this.function.function.apply(algebra.et.imply.cond, index=0)

    Eq << Eq[-1].this.function.function.apply(sets.eq.imply.eq.union_intersection, A[n].set)

    Eq << algebra.imply.all.limits_assert.apply(Eq.size_deduction.function.limits)

    Eq << Eq[-1].this.function.apply(sets.contains.imply.eq.union)

    Eq << algebra.cond.all.imply.all_et.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].this.function.apply(algebra.all.any.imply.any_et)

    Eq << Eq[-1].this.function.function.apply(algebra.et.imply.et.subs)

    Eq << Eq[-1].this.function.function.apply(algebra.et.imply.et.delete, index=1)

    Eq << Eq[-1].this.find(Equal[2]).apply(sets.is_emptyset.imply.notcontains, simplify=None)

    Eq << Eq[-1].this.find(NotContains).apply(sets.notcontains.imply.all_notcontains)

    Eq << Eq[-1].this.function.apply(sets.any.imply.any.limits.relax, wrt=A[n])

    Eq << Eq[-1].this.function.apply(algebra.any_et.imply.any.limits_absorb, index=1)

    Eq << Eq[-1].this.function.apply(sets.any.imply.any.limits.swap)

    Eq << Eq[-1].this.function.function.apply(sets.all_ne.all_ne.imply.all_ne)

    Eq << Eq[-1].this.function.apply(sets.any.imply.any.limits.swap)

    Eq << Eq.induct.induct()

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq.initial, Eq[-1], start=2, n=n)


if __name__ == '__main__':
    run()

from . import two
from . import split
