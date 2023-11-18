import os

import mpmath.libmp as mlib

from sympy.external import import_module

#
# SYMPY_GROUND_TYPES can be gmpy, gmpy2, python or auto
#
GROUND_TYPES = os.environ.get('SYMPY_GROUND_TYPES', 'auto').lower()


#
# Try to import gmpy2 by default. If gmpy or gmpy2 is specified in
# SYMPY_GROUND_TYPES then warn if gmpy2 is not found. In all cases there is a
# fallback based on pure Python int and PythonMPQ that should still work fine.
#
if GROUND_TYPES in ('auto', 'gmpy', 'gmpy2'):

    # Actually import gmpy2
    gmpy = import_module('gmpy2', min_module_version='2.0.0',
                module_version_attr='version', module_version_attr_call_args=())

    # Warn if user explicitly asked for gmpy but it isn't available.
    if gmpy is None and GROUND_TYPES in ('gmpy', 'gmpy2'):
        from warnings import warn
        warn("gmpy library is not installed, switching to 'python' ground types")

elif GROUND_TYPES == 'python':

    # The user asked for python so ignore gmpy2 module.
    gmpy = None

else:

    # Invalid value for SYMPY_GROUND_TYPES. Ignore the gmpy2 module.
    from warnings import warn
    warn("SYMPY_GROUND_TYPES environment variable unrecognised. "
         "Should be 'python', 'auto', 'gmpy', or 'gmpy2'")
    gmpy = None


#
# At this point gmpy will be None if gmpy2 was not successfully imported or if
# the environment variable SYMPY_GROUND_TYPES was set to 'python' (or some
# unrecognised value). The two blocks below define the values exported by this
# module in each case.
#
if gmpy is not None:

    HAS_GMPY = 2
    GROUND_TYPES = 'gmpy'
    SYMPY_INTS = (int, type(gmpy.mpz(0)))
    MPZ = gmpy.mpz
    MPQ = gmpy.mpq

    factorial = gmpy.fac
    sqrt = gmpy.isqrt

else:
    from .pythonmpq import PythonMPQ

    HAS_GMPY = 0
    GROUND_TYPES = 'python'
    SYMPY_INTS = (int,)
    MPZ = int
    MPQ = PythonMPQ

    factorial = mlib.ifac
    sqrt = mlib.isqrt
