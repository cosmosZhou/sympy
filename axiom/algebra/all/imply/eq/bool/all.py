from util import *


@apply
def apply(given):
    assert given.is_ForAll
    return Equal(Bool(given), 1)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(integer=True)
    f = Function(shape=(), integer=True)
    s, A = Symbol(etype=dtype.integer)

    Eq << apply(All[x:A](Element(f(x), s)))

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piece)


if __name__ == '__main__':
    run()

# created on 2018-12-18
