from sympy import *

# Computes the categorical crossentropy loss.


# https://tensorflow.google.cn/api_docs/python/tf/keras/losses/categorical_crossentropy?hl=en
def crossentropy(y_true, y_pred):
    return -y_true @ log(y_pred)
 
  
crossentropy = Function.crossentropy(nargs=(2,), shape=(), real=True, eval=crossentropy)
