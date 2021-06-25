from sympy.core.function import Function
from sympy.functions.elementary.exponential import log

# Computes the categorical crossentropy loss.


# https://tensorflow.google.cn/api_docs/python/tf/keras/losses/categorical_crossentropy?hl=en
def crossentropy(y_true, y_pred):
    return -y_true @ log(y_pred)
 
  
crossentropy = Function.crossentropy(shape=(), real=True, eval=crossentropy)
