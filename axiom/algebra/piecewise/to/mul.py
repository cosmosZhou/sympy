from util import *


@apply
def apply(self):
    ec = self.of(Piecewise)
    
    common_terms = None
    for e, c in ec: 
        if e.is_Mul:
            if common_terms is None:
                common_terms = {*e.args}
            else:
                common_terms &= {*e.args}
        else:
            if common_terms is None:
                common_terms = {e}
            else:
                common_terms &= {e}
    if common_terms:
        args = []
        for e, c in self.args:
            if e.is_Mul:
                e = Mul(*{*e.args} - common_terms)
            elif e.is_Zero:
                ...
            else:
                e = 1
            args.append((e, c))
        rhs = Mul(*common_terms, Piecewise(*args))        
     
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    r = Symbol.r(real=True, given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    g = Function.g(shape=(), real=True)
    f = Function.f(shape=(), real=True)
    h = Function.h(shape=(), real=True)
    Eq << apply(Piecewise((r * g(x), Equal(x, y)), (r * f(x), Contains(y, A)), (r * h(x), True)))

    Eq << algebra.eq.given.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[1].apply(algebra.et.given.et.subs.bool)

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool)

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, 1, invert=True)

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, invert=True)

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, 1, invert=True)

    Eq << Eq[-1].this.args[-1].apply(sets.notcontains.given.notcontains, simplify=False)

    Eq << Eq[-1].this.args[-1].args[-1].simplify()

    Eq << Eq[-1].this.args[-1].args[-1].reversed
    Eq << algebra.ou.given.ou.collect.apply(Eq[-1], cond=Unequal(x, y), simplify=None)


if __name__ == '__main__':
    run()