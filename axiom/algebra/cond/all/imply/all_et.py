from util import *


@apply
def apply(cond, forall):
    if cond.is_Quantifier:
        assert not cond.variables_set & forall.variables_set
        
    fn, *limits = forall.of(All)
    return All(cond & fn, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    y = Symbol(real=True)
    B = Symbol(etype=dtype.real)
    f, g = Function(integer=True)
    Eq << apply(f(y) > 0, All[y:B](g(y) > 0))

    Eq << algebra.all_et.given.et.all.apply(Eq[-1])

    Eq << algebra.all.given.cond.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-12-24
# updated on 2018-12-24
