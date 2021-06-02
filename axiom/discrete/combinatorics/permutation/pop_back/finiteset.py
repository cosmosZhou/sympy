from util import *


@apply
def apply(*given):
    import axiom
    assert len(given) == 2
    set_comprehension_equality, last_element_equality = given

    if last_element_equality.lhs.is_Cup:
        last_element_equality, set_comprehension_equality = set_comprehension_equality, last_element_equality
    p, n = last_element_equality.lhs.of(Indexed)
    a, _n = last_element_equality.rhs.of(Indexed)

    assert n == _n

    set_comprehension_p, set_comprehension_a = set_comprehension_equality.of(Equal)
    _p = axiom.is_set_comprehension(set_comprehension_p)
    _a = axiom.is_set_comprehension(set_comprehension_a)
    assert a[:n + 1] == _a
    assert p[:n + 1] == _p

    return Equal(p[:n].set_comprehension(), a[:n].set_comprehension())


@prove(surmountable=False)
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True, given=True)
    p = Symbol.p(shape=(oo,), etype=dtype.integer, given=True)
    a = Symbol.a(shape=(oo,), etype=dtype.integer, given=True)

    Eq << apply(Equal(p[:n + 1].set_comprehension(), a[:n + 1].set_comprehension()),
                Equal(p[n], a[n]))

    Eq << Eq[0].this.lhs.split(Slice[-1:])

    Eq << Eq[-1].this.rhs.split(Slice[-1:])

    Eq << Eq[-1].subs(Eq[1])

    Eq << sets.eq.imply.eq.complement.apply(Eq[-1], {a[n]})
    return
    Eq << Eq[2].subs(Eq[-1].reversed).reversed

    Eq.plausible = NotContains(n, Eq[-1].rhs, plausible=True)

    Eq << ~Eq.plausible

    Eq << Eq[-1].apply(sets.contains.imply.any_contains.split.cup)

    i = Eq[-1].variable
    _i = i.copy(domain=Range(0, n))
    Eq << Eq[-1].limits_subs(i, _i)

    Eq << Eq[0].lhs.this.split({_i, n})

    Eq.paradox = Eq[-1].subs(Eq[-2].reversed).subs(Eq[1])

    Eq << sets.imply.le.union.apply(*Eq.paradox.function.rhs.args)

    Eq << sets.imply.le.cup.apply(*Eq.paradox.function.rhs.args[1].args)

    Eq << Eq[-2] + Eq[-1]

    Eq << Eq.paradox.apply(algebra.eq.imply.eq.abs)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << sets.notcontains.imply.eq.complement.apply(Eq.plausible)


if __name__ == '__main__':
    run()
