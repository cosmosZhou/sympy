from util import *


@apply
def apply(imply):
    assert imply.expr.is_And

    limits_dict = imply.limits_dict
    for i, eq in enumerate(imply.expr.args):
        if eq.is_Equal:
            if eq.lhs in limits_dict:
                old, new = eq.args
            elif eq.rhs in limits_dict:
                new, old = eq.args
            else:
                continue

            limits = imply.limits_delete(old)
            if any(limit._has(old) for limit in limits):
                continue

            eqs = [*imply.expr.args]
            del eqs[i]
            eqs = [eq._subs(old, new) for eq in eqs]

            domain = limits_dict[old]
            if isinstance(domain, list):
                limit = (old,)
            else:
                limit = (old, domain)
            eq = imply.func(eq, limit).simplify()
            eqs.append(eq)

            return Any(And(*eqs), *limits)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    k = Symbol.k(integer=True)
    j = Symbol.j(domain=Range(0, k))
    x = Symbol.x(real=True, shape=(oo,))
    f = Function.f(shape=(), integer=True)
    f_quote = Function("f'", shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    Eq << apply(Any[x[:n]:f(x[:n]) > 0, i:k]((g(i) > f_quote(j, x[:n])) & Equal(i, j)))

    Eq << Eq[-1].this.expr.apply(algebra.cond.imply.any_et, wrt=j)

    Eq << Eq[-1].this.expr.apply(algebra.et.imply.et.invoke, algebra.eq.cond.imply.cond.kroneckerDelta, delta=False, simplify=None, swap=True, ret=1)

    Eq << algebra.any.imply.any.limits.swap.apply(Eq[-1], simplify=None)

    Eq << Eq[0].this.expr.apply(algebra.et.given.et.split.eq, delta=False, simplify=None)


if __name__ == '__main__':
    run()

