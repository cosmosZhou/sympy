"""
SymPy is a Python library for symbolic mathematics. It aims to become a
full-featured computer algebra system (CAS) while keeping the code as simple
as possible in order to be comprehensible and easily extensible.  SymPy is
written entirely in Python. It depends on mpmath, and other external libraries
may be optionally for things like plotting support.

See the webpage for more information and documentation:

    https://sympy.org

"""
# Fore: BLACK, RED, GREEN, YELLOW, BLUE, MAGENTA, CYAN, WHITE, RESET.
# Back: BLACK, RED, GREEN, YELLOW, BLUE, MAGENTA, CYAN, WHITE, RESET.
# Style: DIM, NORMAL, BRIGHT, RESET_ALL

class Style:
    default = '0'
    bright = '1'
    nonbold = '22'
    underline = '4'
    nonunderline = '24'
    blink = '5'
    nonblink = '25'
    revert = '7'
    nonrevert = '27'

class Foreground:
    BLACK = '30' 
    RED = '31'
    GREEN = '32'
    YELLOW = '33'
    BLUE = '34'
    MAGENTA = '35'
    CYAN = '36'
    WHITE = '37'

class Background:
    BLACK = '40' 
    RED = '41'
    GREEN = '42'
    YELLOW = '43'
    BLUE = '44'
    MAGENTA = '45'
    CYAN = '46'
    WHITE = '47'

def println(*message, **kwargs):
    style = ';'.join(kwargs.values())
    print("\033[%sm%s\033[0m" % (style, ' '.join(message)))

    

import sys
if sys.version_info < (3, 6):
    raise ImportError("Python version 3.6 or above is required for SymPy.")
del sys


try:
    import mpmath
except ImportError:
    raise ImportError("SymPy now depends on mpmath as an external library. "
    "See https://docs.sympy.org/latest/install.html#mpmath for more information.")

del mpmath

from sympy.release import __version__

if 'dev' in __version__:

    def enable_warnings():
        import warnings
        warnings.filterwarnings('default', '.*', DeprecationWarning, module='sympy.*')
        del warnings

    enable_warnings()
    del enable_warnings


def __sympy_debug():
    # helper function so we don't import os globally
    import os
    debug_str = os.getenv('SYMPY_DEBUG', 'False')
    if debug_str in ('True', 'False'):
        return eval(debug_str)
    else:
        raise RuntimeError("unrecognized value for SYMPY_DEBUG: %s" %
                           debug_str)


SYMPY_DEBUG = __sympy_debug()  # type: bool

from .core import *
from .logic import *
from .assumptions import *
from .polys import *
from .series import *
from .functions import *
from .ntheory import *
from .concrete import *
from .discrete import *
from .simplify import *
from .sets import *
from .solvers import *
from .matrices import *
from .geometry import *
from .utilities import *
from .integrals import *
from .tensor import *
from .parsing import *
from .calculus import *
from .algebra import *
from .stats import *
from .keras import *
# This module causes conflicts with other modules:
# from .stats import *
# Adds about .04-.05 seconds of import time
# from combinatorics import *
# This module is slow to import:
#from physics import units
from .plotting import plot, textplot, plot_backends, plot_implicit
from .printing import *
from .interactive import init_session, init_printing

evalf._create_evalf_table()

# This is slow to import:
# import abc