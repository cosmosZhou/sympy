from util import *


def new(p, q, simplify=True):    
    if simplify:
        if q.is_Infer:
            _p, q = q.args
            p &= _p
        cond = Infer(p, q)
        cond = cond.simplify()
    else:
        cond = Infer(p, q)
    return cond

@apply
def apply(given, index=-1, *, simplify=True):
    fx, fy = given.of(Infer)
    eqs = fy.of(And)
    
    
    if index is not None:
        first = eqs[:index]
        second = eqs[index:]
    
        first = And(*(new(fx, eq, simplify) for eq in first))
        second = And(*(new(fx, eq, simplify) for eq in second))
        return first, second
    
    return tuple(new(fx, eq, simplify) for eq in eqs)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    f, h, g = Function(integer=True)
    Eq << apply(Infer(Equal(h(x), h(y)), Equal(f(x), f(y)) & Equal(g(x), g(y))))

    Eq << Eq[0].this.rhs.apply(algebra.et.imply.cond, index=0)

    Eq << Eq[0].this.rhs.apply(algebra.et.imply.cond, index=1)


if __name__ == '__main__':
    run()
# created on 2018-08-16
# updated on 2018-08-16
