from sympy.core.function import Function

@Function
def clip(a, a_min, a_max):
    from sympy.functions.elementary.miscellaneous import Min, Max
    return Min(a_max, Max(a, a_min))
