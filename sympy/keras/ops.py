from sympy.functions.elementary.miscellaneous import Min, Max
from sympy.core.function import Function


def clip(a, a_min, a_max):
    return Min(a_max, Max(a, a_min))


clip = Function.clip(shape=(), eval=clip)


