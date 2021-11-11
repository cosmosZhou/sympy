from util import *


@apply
def apply(imply, index=-1, invert=None, reverse=False):
    assert imply.is_Boolean

    eqs = imply.of(And)

    given = eqs[index]

    imply = []
    if isinstance(index, int):
        if index < 0:
            index += len(eqs)

        for i in range(len(eqs)):
            if i == index:
                continue
            imply.append(eqs[i])
    elif isinstance(index, slice):
        given = And(*given)
        start, stop = index.start, index.stop
        if start is None:
            start = 0
        if stop is None:
            stop = len(eqs)
        for i in {*range(len(eqs))} - {*range(start, stop)}:
            imply.append(eqs[i])
    else:
        return

    imply = And(*imply)

    if invert:
        old = given.invert()
        new = S.BooleanFalse
    else:
        old = given
        new = S.BooleanTrue

    if reverse:
        old = old.reversed

    return given, imply._subs(old, new)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)
    f, g, h = Function(shape=(), integer=True)
    Eq << apply(Equal(Piecewise((f(x), NotElement(x, S)), (g(x), True)), h(x)) & NotElement(x, S))

    Eq << Equal(Bool(NotElement(x, S)), 1, plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piece)

    Eq << Equal(Piecewise((f(x), Equal(Bool(NotElement(x, S)), 1)), (g(x), True)), h(x), plausible=True)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.swap)

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

# created on 2018-01-19
# updated on 2018-01-19
