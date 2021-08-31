from util import *


@apply
def apply(self):
    for i, lamda in enumerate(self.of(Add)):
        if lamda.is_Lamda:
            variables = lamda.variables
            args = [*self.args]
            del args[i]
            rest = self.func(*args)
            if rest.shape:
                size = min(len(rest.shape), len(variables))
                variables = variables[:size]
                rest = rest[variables[::-1]]

            rhs = Lamda(rest + lamda.expr, *lamda.limits)
            break

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(integer=True)
    g = Symbol(shape=(n, n), integer=True)
    Eq << apply(Lamda[i:n, j:n](f(j, i)) + g)

    i, j = Symbol(domain=Range(0, n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j)


if __name__ == '__main__':
    run()
