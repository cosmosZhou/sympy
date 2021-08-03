from util import *


@apply
def apply(cond, exists):
    if not exists.is_Any:
        cond, exists = exists, cond

    if cond.is_Quantifier:
        assert not cond.variables_set & exists.variables_set

    fn, *limits = exists.of(Any)

    return Any(cond & fn, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    y = Symbol.y(real=True)

    B = Symbol.B(etype=dtype.real, given=True)

    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(f(y) > 0, Any[y:B](g(y) > 0))

    Eq << ~Eq[-1].simplify()

    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq[1])

    Eq << algebra.any_et.imply.any.split.apply(Eq[-1], index=0)

    Eq << ~Eq[-1]

    Eq << algebra.cond.imply.all.restrict.apply(Eq[0], (y, B))


if __name__ == '__main__':
    run()

