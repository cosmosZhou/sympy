from util import *


@apply
def apply(P):
    definition = P.definition
    assert definition.is_ConditionSet
    x = definition.variable

    return ForAll[x:P](definition.condition & Contains(x, definition.base_set))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    x = Symbol.x(shape=(oo,), integer=True)

    f = Function.f(nargs=(n,), shape=(), integer=True)

    P = Symbol.P(conditionset(x[:n], f(x[:n]) > 0, CartesianSpace(Range(0, m), n)))
    Eq << apply(P)

    Eq << algebra.all_et.imply.all.apply(Eq[-1])

    Eq << ForAll[x[:n]:P](Contains(x[:n], P), plausible=True)

    Eq << Eq[-1].simplify()

    Eq << Eq[-1].this.function.rhs.definition


if __name__ == '__main__':
    run()

