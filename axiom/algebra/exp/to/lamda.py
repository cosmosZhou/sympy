from util import *


@apply
def apply(self):
    arg = self.of(Exp)
    if arg.is_Mul:
        [*args] = arg.args
        for i, lamda in enumerate(args):
            if lamda.is_Lamda:
                break
        else:
            return
        del args[i]
        coeff = Mul(*args)
        f, *limits = lamda.of(Lamda)
        f *= coeff
    else:
        f, *limits = arg.of(Lamda)

    return Equal(self, Lamda(exp(f), *limits), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    h = Symbol(integer=True, shape=(n,))
    Eq << apply(exp(Lamda[i:n](h[i])))

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)





if __name__ == '__main__':
    run()
# created on 2021-12-19
