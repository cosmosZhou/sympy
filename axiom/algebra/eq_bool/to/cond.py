from util import *



@apply(given=None)
def apply(given):
    boole, one = given.of(Equal)
    if not one.is_One:
        boole, one = one, boole
    assert one.is_One

    cond = boole.of(Bool)

    return Equivalent(given, cond)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)

    Eq << apply(Equal(Bool(Element(x, A)), 1))

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)


if __name__ == '__main__':
    run()
# created on 2019-04-21
