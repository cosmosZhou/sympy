from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets, calculus


@apply(imply=True)
def apply(x, y):
    return Equality(cos(x + y), cos(x) * cos(y) - sin(x) * sin(y))        


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
        
    Eq << apply(x, y)
    
    Eq << Eq[0].this.lhs.apply(calculus.trigonometry.euler.cosine)
    
    Eq << Eq[-1].this.rhs.args[0].args[0].apply(calculus.trigonometry.euler.cosine)
    
    Eq << Eq[-1].this.rhs.args[0].args[1].apply(calculus.trigonometry.euler.cosine)
    
    Eq << Eq[-1].this.rhs.args[1].args[1].apply(calculus.trigonometry.euler.sine)
    
    Eq << Eq[-1].this.rhs.args[1].args[-1].apply(calculus.trigonometry.euler.sine)
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.lhs.expand()

    
# https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F
if __name__ == '__main__':
    prove(__file__)
