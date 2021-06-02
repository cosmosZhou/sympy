from util import *

import axiom
from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(A): 
    assert A.is_alpha
    assert len(A.args) == 1
    mat = A.arg
    assert mat.is_Matrix
    
    return Equal(A, alpha(*mat._args))


@prove
def prove(Eq): 
    x = Symbol.x(real=True, positive=True, shape=(oo,))    
    Eq << apply(alpha(Matrix((x[0], x[1], x[2]))))
    
    Eq << Eq[-1].this.find(alpha).defun()
    
    Eq << Eq[-1].this.find(alpha).defun()
    
    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()
    
    Eq << Eq[-1].this.find(alpha).defun()
    
    Eq << Eq[-1].this.find(alpha).defun()
    
if __name__ == '__main__':
    run()


