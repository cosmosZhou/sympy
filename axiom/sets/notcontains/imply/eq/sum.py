from util import *


@apply
def apply(given, sgm):
    e, S = given.of(NotContains)
    fx, (x, _S) = sgm.of(Sum)
    _e = _S.of(Union[S, FiniteSet])
    assert _e == e    
    return Equal(Sum[x:S | {e}](fx), Sum[x:S](fx) + fx._subs(x, e))


@prove
def prove(Eq):
    from axiom import sets, algebra

    S = Symbol.S(etype=dtype.integer)
    e = Symbol.e(integer=True)
    x = Symbol.x(integer=True)
    f = Function.f(integer=True)
    Eq << apply(NotContains(e, S), Sum[x:S | {e}](f(x)))

    Eq << sets.notcontains.imply.is_emptyset.intersection.apply(Eq[0])

    Eq << Eq[1].this.lhs.apply(algebra.sum.to.add.split, cond={e})

    Eq << sets.notcontains.imply.eq.complement.apply(Eq[0])
    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()