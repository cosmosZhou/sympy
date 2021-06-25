from util import *



@apply
def apply(given, *limits):
    limits = [*limits]
    for i, (x, *ab) in enumerate(limits):
        if not ab:
            if x.domain:
                limits[i] = (x, x.domain)
    return All(given, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(f(e) > 0, (e, S))

    Eq << Eq[0].apply(algebra.cond.imply.et.all, cond=Contains(e, S))

    Eq << algebra.et.imply.conds.apply(Eq[-1])


if __name__ == '__main__':
    run()

