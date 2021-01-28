from __future__ import absolute_import, print_function, unicode_literals

import numpy
from sympy.matrices.dense import Matrix


class PackedArray(numpy.ndarray):
    """ Wrapper class on top of NymPy ndarray used to preserve packed arrays when round-tripping them. """
    def sympify(self):
        if len(self.shape) == 1:
            return Matrix([*self])
        if len(self.shape) == 2:
            ...