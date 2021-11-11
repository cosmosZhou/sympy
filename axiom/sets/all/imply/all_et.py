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

    x = Symbol(real=True)
    f = Function(real=True)
    S = Symbol(etype=dtype.real, given=True)
    Eq << apply(All[x:S](f(x) > 0))

    Eq << algebra.all_et.given.et.all.apply(Eq[-1], simplify=None)

    

    

    


if __name__ == '__main__':
    run()
# created on 2020-04-21
# updated on 2020-04-21
