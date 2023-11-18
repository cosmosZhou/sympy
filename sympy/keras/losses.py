from sympy.core.function import Function


# Computes the categorical crossentropy loss.
# https://tensorflow.google.cn/api_docs/python/tf/keras/losses/categorical_crossentropy?hl=en
@Function(shape=(), real=True)
def crossentropy(y_true, y_pred):
    from sympy.functions.elementary.exponential import log
    return -y_true @ log(y_pred)
