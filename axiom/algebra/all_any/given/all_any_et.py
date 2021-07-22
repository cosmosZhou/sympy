from util import *


@apply
def apply(imply):
    from sympy.concrete.limits import limits_cond
    (fn, *limits_e), *limits_f = imply.of(All[Any])
    cond = limits_cond(limits_f)
    return All(Any(fn & cond, *limits_e), *limits_f)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(shape=(), integer=True)    
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    Eq << apply(All[x:A](Any[y:B](f(x, y) > 0)))  
    
    Eq << Eq[1].this.expr.simplify()    


if __name__ == '__main__':
    run()

