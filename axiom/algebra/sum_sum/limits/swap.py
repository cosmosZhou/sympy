from util import *


@apply
def apply(self):
    [*args], *limits = self.of(Sum[Mul])
    
    for index in range(len(args)):
        if args[index].is_Sum:
            break
    else:
        return
    
    sgm = args.pop(index)
    if isinstance(sgm.function, Mul):
        args.extend(sgm.function.args)
    else:
        args.append(sgm.function)
        
    function = Mul(*args).powsimp()
    independent, dependent = function.as_independent(*(x for x, *_ in self.limits), as_Add=False)
    if independent == S.One:
        rhs = sgm.func(Sum(function, *limits), *sgm.limits)
    else:
        rhs = sgm.func(independent * Sum(dependent, *limits), *sgm.limits)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    g = Symbol.g(shape=(oo, oo), real=True)
    h = Symbol.h(shape=(oo,), real=True)
    Eq << apply(Sum[i:m](h[i] * Sum[j:n](g[i, j])))

    Eq << Eq[0].this.lhs.function.apply(algebra.mul.to.sum)
    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.swap)


if __name__ == '__main__':
    run()
