from sympy import *


def clip(a, a_min, a_max):
    return Min(a_max, Max(a, a_min))


clip = Function.clip(nargs=(3,), shape=(), eval=clip)


