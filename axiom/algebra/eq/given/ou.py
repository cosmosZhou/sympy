from util import *



@apply
def apply(imply):
    piecewise, sym = imply.of(Equal)
    if sym.is_Piecewise:
        piecewise, sym = sym, piecewise

    piecewise = piecewise.of(Piecewise)

    univeralSet = S.BooleanTrue
    args = []

    for expr, cond in piecewise:
        condition = cond & univeralSet
        if not cond:
            invert = condition.invert()
            univeralSet &= invert

        eq = condition & imply.func(sym, expr).simplify()
        args.append(eq)

    return Or(*args)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real * k, given=True)

    f, g, h = Function(shape=(k,), real=True)

    Eq << apply(Equal(p, Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True))))

    Eq << algebra.ou.imply.eq.piece.apply(Eq[1], wrt=p)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

