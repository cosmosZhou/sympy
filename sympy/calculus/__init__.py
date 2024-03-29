"""Calculus-related methods."""

from .euler import euler_equations
from .singularities import (singularities, is_increasing,
                            is_strictly_increasing, is_decreasing,
                            is_strictly_decreasing, is_monotonic)
from .finite_diff import finite_diff_weights, apply_finite_diff, as_finite_diff, differentiate_finite
from .util import (periodicity, not_empty_in, AccumBounds, is_convex,
                   stationary_points, minimum, maximum)
