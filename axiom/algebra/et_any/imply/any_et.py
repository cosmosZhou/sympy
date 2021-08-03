from util import *


@apply(simplify=None)
def apply(given):
    [*eqs] = given.of(And)
    for i, eq in enumerate(eqs):
        if eq.is_Any:
            break
    else:
        return
    exists = eqs.pop(i)
    f, *limits = exists.of(Any)
    f = And(*eqs, f)
    return Any(f, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    h = Function.h(real=True)
    b = Symbol.b(shape=(k,), real=True)
    B = Symbol.B(etype=dtype.real * k, given=True)
    Eq << apply(And(Unequal(x, y), Unequal(f(x), g(y)), Any[b:B](Equal(f(x), h(b)))))

    Eq << Eq[0].this.args[1:].apply(algebra.cond.any.imply.any_et, simplify=None)

    Eq << Eq[-1].this.apply(algebra.cond.any.imply.any_et, simplify=None)


if __name__ == '__main__':
    run()