from util import *


def doit(Sum, self):
    function, * limits, (i, si) = self.of(Sum)
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

    return Sum(function, *limits)


@apply
def apply(self):
    return Equal(self, doit(Sum, self))


@prove
def prove(Eq):
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    f = Function.f(integer=True)
    a = Symbol.a(integer=True)
    Eq << apply(Sum[j:f(i), i:{a}](x[i, j]))

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()

