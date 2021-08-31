from util import *



@apply
def apply(self, *, cond=None):
    cond=sympify(cond)

    matched = []
    unmatch = []
    for eq in self.args:
        if eq.is_Or:
            if cond in eq.args:
                matched.append(Or(*eq._argset - {cond}))
                continue
        elif eq == cond:
            matched.append(S.false)
            continue
        unmatch.append(eq)
    assert not unmatch
    return Or(cond, self.func(*matched))


@prove
def prove(Eq):
    from axiom import algebra
    a, b, c, d = Symbol(integer=True, given=True)


    x, y = Symbol(real=True, given=True)

    f, g = Function(real=True)

    Eq << apply(And((a < b) | (c < d), (f(x) < g(y)) | (c < d), (x < y) | (c < d)), cond=c < d)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]

    Eq << algebra.et.imply.ou.apply(Eq[-1])


if __name__ == '__main__':
    run()

