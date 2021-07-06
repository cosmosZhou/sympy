from util import *


@apply
def apply(cond, exists):
    (fn, *limits_e), *limits_f = exists.of(Any[All])
    
    assert not cond.has(*(e for e, *_ in limits_e))
    assert not cond.has(*(e for e, *_ in limits_f))
    
    return Any(All(cond & fn, *limits_e), *limits_f)


@prove
def prove(Eq):
    from axiom import algebra

    y = Symbol.y(real=True)
    x = Symbol.x(real=True)
    B = Symbol.B(etype=dtype.real, given=True)
    A = Symbol.A(etype=dtype.real, given=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    h = Function.h(shape=(), integer=True)
    Eq << apply(h(A, B) > 0, Any[y:B](All[x:A]((g(x, y) > 0))))

    Eq << Eq[-1].this.function.apply(algebra.all_et.given.et.all, simplify=None)

    Eq <<~ Eq[-1]

    Eq << algebra.cond.all.imply.all_et.apply(Eq[0], Eq[-1], simplify=None)

    Eq << algebra.all_et.imply.et.all.apply(Eq[-1])
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()