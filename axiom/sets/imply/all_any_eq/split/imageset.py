from util import *



@apply
def apply(self):
    variables, expr, base_set = self.image_set()

    if isinstance(base_set, Symbol):
        element_symbol = self.element_symbol()
        assert expr.type == element_symbol.type
        condition = Equal(expr, element_symbol)
        return All(Any(condition, (variables, base_set)), (element_symbol, self))


@prove
def prove(Eq):
    from axiom import algebra, sets

    e = Symbol(etype=dtype.integer.set)
    s = Symbol(etype=dtype.integer.set.set)
    f = Function(etype=dtype.integer.set)
    S = Symbol(imageset(e, f(e), s))
    Eq << apply(S)

    Eq << algebra.all.given.infer.apply(Eq[1])

    Eq << Eq[-1].this.lhs.rhs.definition
    Eq << Eq[-1].this.lhs.apply(sets.el.imply.any_eq.split.imageset)

    Eq << Eq[-1].this.args[0].expr.reversed


if __name__ == '__main__':
    run()

# created on 2020-08-13
