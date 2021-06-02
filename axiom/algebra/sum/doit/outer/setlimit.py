from util import *


import axiom


def doit(self):
    function, *limits = self.args
    * limits, setlimit = limits
    i, si = axiom.limit_is_set((setlimit,))
    i0 = si.of(FiniteSet)

    for t in range(-1, -len(limits) - 1, -1):
        j, *ab = limits[t]
        if not ab:
            ...
        elif len(ab) == 1:
            domain = ab[0]
            if domain.is_boolean:
                if j == i:
                    break

            domain = domain._subs(i, i0)
            limits[t] = (j, domain)
        else:
            a, b = ab
            b = b._subs(i, i0)

            if a.is_boolean:
                if j == i:
                    limits[t] = (j, a, b)
                    break

            a = a._subs(i, i0)
            limits[t] = (j, a, b)

        if j == i:
            break
    else:
        function = function._subs(i, i0)

    return self.func(function, *limits)


@apply
def apply(self):
    assert self.is_Sum

    return Equal(self, doit(self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    f = Function.f(integer=True)

    a = Symbol.a(integer=True)

    Eq << apply(Sum[j:f(i), i:{a}](x[i, j]))

    s = Function.s(eval=lambda i: Sum[j:f(i)](x[i, j]))
    Eq << s(i).this.defun()

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, {a}))

    Eq << Eq[-1].this.lhs.defun()

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

