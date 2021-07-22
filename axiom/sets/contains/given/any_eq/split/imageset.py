from util import *


@apply
def apply(imply):
    from axiom.sets.contains.given.contains.split.imageset import subs_limits_with_epitome
    e, S = imply.of(Contains)

    image_set = S.image_set()

    variables, expr, base_set = image_set
    e = subs_limits_with_epitome(e, expr)
    if e._has(variables):
        _variables = base_set.element_symbol(e.free_symbols)
        assert _variables.type == variables.type
        expr = expr._subs(variables, _variables)
        variables = _variables
    assert not e._has(variables)
    return Any(Equal(e, expr, evaluate=False), (variables, base_set))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    S = Symbol.S(etype=dtype.integer)
    Eq << apply(Contains(y, imageset(x, f(x), S)))

    Eq << Eq[1].simplify()

    Eq << algebra.imply.all.limits_assert.apply(Eq[1].limits)

    Eq << Eq[-1].this.expr.apply(sets.contains.imply.contains.imageset, f=f)

    Eq << algebra.any_eq.all.imply.any.subs.apply(Eq[1].reversed, Eq[-1])
    Eq << algebra.et.imply.et.apply(Eq[-1])


if __name__ == '__main__':
    run()

