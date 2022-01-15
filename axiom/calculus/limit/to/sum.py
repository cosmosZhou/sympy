from util import *


def doit(cls, self, simplify=True):
    from sympy.concrete.limits import limits_dict
    (expr, *limits), limit = self.of(Limit[cls])

    x = limit[0]
    assert x not in limits_dict(limits)
    expr = Limit(expr, limit)
    if simplify:
        expr = expr.doit()

    for i, (x, *ab) in enumerate(limits):
        for j, t in enumerate(ab):
            t = Limit(t, limit)
            if simplify:
                t = t.doit()
            ab[j] = t
        limits[i] = (x, *ab)


    return cls(expr, *limits)

@apply
def apply(self, simplify=True):
    return Equal(self, doit(Sum, self, simplify=simplify), evaluate=False)


@prove(proved=False)
def prove(Eq):
    k, n = Symbol(integer=True)
    s = Function(real=True)
    Eq << apply(Limit[n:oo](Sum[k:n](s(k))))


if __name__ == '__main__':
    run()
# created on 2020-03-15
