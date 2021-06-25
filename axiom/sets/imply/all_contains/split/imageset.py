from util import *



@apply
def apply(self):
    image_set = self.image_set()
    variables, expr, base_set = image_set

    if isinstance(base_set, Symbol):
        return All(Contains(expr, self), (variables, base_set))

@prove
def prove(Eq):
    from axiom import sets, algebra
    e = Symbol.e(etype=dtype.integer.set)
    s = Symbol.s(etype=dtype.integer.set.set)
    f = Function.f(etype=dtype.integer.set)
    S = Symbol.S(imageset(e, f(e), s))
    Eq << apply(S)

    Eq << algebra.all.given.suffice.apply(Eq[1])

    Eq << Eq[-1].this.lhs.apply(sets.contains.imply.contains.imageset, f)

    Eq << Eq[-1].this.rhs.rhs.definition


if __name__ == '__main__':
    run()

