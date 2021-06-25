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
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    B = Symbol.B(etype=dtype.real * k, given=True)

    f = Function.f(shape=(k,), real=True)
    g = Function.g(shape=(k,), real=True)
    h = Function.h(shape=(k,), real=True)
    p = Symbol.p(real=True, shape=(k,), given=True)

    Eq << apply(Equal(p, Piecewise((f(x), Contains(x, A)), (g(x), Contains(x, B)), (h(x), True))))

    Eq << algebra.ou.imply.eq.apply(Eq[1], wrt=p)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

