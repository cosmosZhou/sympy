from util import *


@apply
def apply(piecewise, i=0, pivot=-1):
    [*ecs] = piecewise.of(Piecewise)

    ei, ci = ecs[i]
    eqs = ci.of(Or)
    former = eqs[:pivot]
    latter = eqs[pivot:]
    former = Or(*former)
    latter = Or(*latter)
    ecs[i] = (ei, former)
    ecs.insert(i + 1, (ei, latter))
    from axiom.algebra.piece.swap import swap
    ecs = swap(ecs, i + 1)   
 
    last = Piecewise(*ecs[i + 1:])
    ecs = ecs[:i + 2]
    ecs[-1] = (last, True)
    return Equal(piecewise, Piecewise(*ecs), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,))
    A, B = Symbol(etype=dtype.real * k)
    f, g = Function(shape=(), real=True)
    Eq << apply(Piecewise((f(x), Element(x, A) | Unequal(A, B)), (g(x), True)))

    
    Eq << Eq[0].this.rhs.apply(algebra.piece.flatten)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.swap, 1)


if __name__ == '__main__':
    run()
# created on 2022-01-03
