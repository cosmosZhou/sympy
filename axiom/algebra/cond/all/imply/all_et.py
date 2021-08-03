from util import *


@apply
def apply(cond, forall):
    if not forall.is_All:
        cond, forall = forall, cond

    if cond.is_Quantifier:
        assert not cond.variables_set & forall.variables_set
        
    fn, *limits = forall.of(All)
    return All(cond & fn, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    y = Symbol.y(real=True)
    B = Symbol.B(etype=dtype.real)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    Eq << apply(f(y) > 0, All[y:B](g(y) > 0))

    Eq << algebra.all_et.given.all.apply(Eq[-1])

    Eq << algebra.all.given.cond.apply(Eq[-1])


if __name__ == '__main__':
    run()

