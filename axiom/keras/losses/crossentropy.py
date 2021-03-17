from sympy import *
from tensorflow.nn import softmax
from axiom.utility import prove, apply
from axiom import algebre, calculus
import tensorflow as tf


@apply
def apply(given):
    assert isinstance(given, Equality)
    lhs = given.lhs
    assert isinstance(lhs, summations.Sum)
    
    limit = lhs.limits[0]
    j, a, b = limit
    n = b - a
    
    t = LAMBDA[j:0:n](lhs.function).simplify()    
    
    assert n >= 2
    
    x = Symbol.x(shape=(n,), real=True)    
    y = Symbol.y(softmax(x))
    
    assert y.is_zero == False
    
    return Equality(Derivative(tf.crossentropy(t, y), x), y - t)


@prove
def prove(Eq):
    n = Symbol.n(domain=Interval(2, oo, integer=True))    
    t = Symbol.t(shape=(n,), real=True)
    j = Symbol.j(integer=True)
    given = Equality(Sum[j:0:n](t[j]), 1)
    
    Eq << apply(given)
    assert Eq[0].lhs.is_zero == False
    
    Eq << Eq[-1].lhs.expr.this.definition
    
    Eq << Eq[-1].this.rhs.args[1].expand(free_symbol=j)
    
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    xi = Eq[2].lhs._wrt_variables[0][i]

    assert Eq[-1].lhs.has(xi)
    
    Eq << Eq[-1].apply(calculus.eq.imply.eq.derive, (xi,), simplify=False)    
    
    Eq.loss = Eq[-1].this.rhs.doit(deep=False)            
    
    i = xi.indices[0]
    Eq << Eq[0][i]
    
    Eq << Eq[0][j]
    
    assert Eq[0].lhs.is_zero == False
    
    assert Eq[-1].lhs.is_zero == False
    
    Eq << Eq[-1].apply(calculus.eq.imply.eq.derive, (xi,), simplify=False)
    
    assert Eq[-1].lhs.expr.is_zero == False
    
    Eq << Eq[-1].this.rhs.doit(deep=False)
    
    assert Eq[-1].lhs.expr.is_zero == False
    
    Eq << Eq[-1].subs(Eq[-3].reversed).subs(Eq[-4].reversed) / Eq[-1].lhs.expr
    
    Eq.loss = Eq.loss.subs(Eq[-1]).expand()
    
    Eq.loss = Eq.loss.this.rhs.args[0].simplify()
    
    Eq.loss = Eq.loss.this.rhs.args[1].args[1].simplify()
    
    Eq.loss = Eq.loss.subs(given)
    
    Eq << algebre.eq.imply.eq.lamda.apply(Eq.loss, (i,), simplify=False)

    
if __name__ == '__main__':
    prove(__file__)
