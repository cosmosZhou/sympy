from util import *


def flatten(piecewise, index=None):
    if index is None:
        for index, (e, c) in enumerate(piecewise.args):
            if e.is_Piecewise:
                break
        else:
            return piecewise

        _piecewise = flatten(piecewise, index)
        if _piecewise is piecewise:
            return piecewise
        return flatten(_piecewise)

    expr, cond = piecewise.args[index]
    _ec = expr.of(Piecewise)

    _ec = tuple((e, c & cond) for e, c in _ec)
    ec_before = piecewise.args[:index]

    if index < 0:
        index += len(piecewise.args)

    ec_after = piecewise.args[index + 1:]
    return piecewise.func(*ec_before + _ec + ec_after)


@apply
def apply(piecewise, index=None):
    return Equal(piecewise, flatten(piecewise, index))


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,))
    A, B = Symbol(etype=dtype.real * k)
    f, g, h = Function(shape=(), real=True)
    #Eq << apply(Piecewise((f(x), Element(x, A)), (Piecewise((g(x), Element(x, B)), (h(x), True)), True)))
    Eq << apply(Piecewise((Piecewise((g(x), Element(x, B)), (h(x), True)), Element(x, A)), (f(x), True)))

    p = Symbol(Eq[0].lhs)
    Eq << p.this.definition

    Eq << algebra.eq_piece.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].args[0].apply(algebra.eq_piece.imply.ou)

    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)

    Eq << algebra.ou.imply.eq.piece.apply(Eq[-1], wrt=p)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.swap)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.swap, -2)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-01-20
# updated on 2018-01-20
