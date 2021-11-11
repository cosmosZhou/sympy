from util import *


@apply
def apply(cond, exists):
    if cond.is_Quantifier:
        assert not cond.variables_set & exists.variables_set

    fn, *limits = exists.of(Any)

    return Any(cond & fn, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    y = Symbol(real=True)

    B = Symbol(etype=dtype.real, given=True)

    f, g = Function(shape=(), integer=True)

    Eq << apply(f(y) > 0, Any[y:B](g(y) > 0))

    Eq << ~Eq[-1].simplify()

    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq[1])

    Eq << algebra.any_et.imply.any.split.apply(Eq[-1], index=0)

    Eq << ~Eq[-1]

    Eq << algebra.cond.imply.all.restrict.apply(Eq[0], (y, B))


if __name__ == '__main__':
    run()

# created on 2018-04-11
# updated on 2018-04-11
