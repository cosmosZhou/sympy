from util import *


def limits_subs(cls, self, offset, simplify=True):
    fx, (x, *ab), *limits = self.of(cls)
    fx = fx._subs(x, x + offset)
    if len(ab) == 2:
        a, b = ab
        if a.is_bool:
            a = a._subs(x, x + offset)
            b -= offset
        else:
            a -= offset
            b -= offset
        limit = (x, a, b)
    elif ab:
        [domain] = ab
        if domain.is_bool:
            domain = domain._subs(x, x + offset)
        else:
            domain -= offset
        limit = (x, domain)
    else:
        limit = (x,)
    self = cls(fx, limit, *limits)
    if simplify:
        self = self.simplify()
    return self

@apply
def apply(self, offset):
    return Equal(self, limits_subs(Sum, self, offset), evaluate=False)


@prove
def prove(Eq):
    a, b, n, d = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(Sum[n:a:b](f(n)), d)

    Eq << Eq[0] - Eq[0].lhs


if __name__ == '__main__':
    run()
# created on 2018-04-28
