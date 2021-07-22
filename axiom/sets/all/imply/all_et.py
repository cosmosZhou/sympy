from util import *


@apply
def apply(given):
    fn, (x, *S) = given.of(All)
    if len(S) == 1:
        [S] = S
        assert S.is_set
    else:
        S = Range(*S) if x.is_integer else Interval(*S)
    return All[x:S](fn & Unequal(S, x.emptySet))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    f = Function.f(real=True)
    S = Symbol.S(etype=dtype.real, given=True)
    Eq << apply(All[x:S](f(x) > 0))

    Eq << algebra.all_et.given.all.apply(Eq[-1], simplify=None)

    Eq << ~Eq[-1]

    Eq << algebra.any.imply.any_et.limits.single_variable.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs)


if __name__ == '__main__':
    run()