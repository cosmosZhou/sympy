from util import *



@apply
def apply(given, index):
    x, S = given.of(Element)
    a = given.generate_var(**x.type.dict)
    return Any[a:S](Equal(x[index], a[index]))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(positive=True, integer=True)
    x = Symbol(integer=True, shape=(n,))
    i = Symbol(integer=True)
    S = Symbol(etype=dtype.integer * n)

    Eq << apply(Element(x, S), index=i)

    a = Eq[-1].variable

    Eq << algebra.any.given.any.subs.apply(Eq[-1], a, x)

    Eq << sets.any_el.given.ne_empty.apply(Eq[-1])

    Eq << sets.el.imply.ne_empty.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2021-03-02
# updated on 2021-03-02
