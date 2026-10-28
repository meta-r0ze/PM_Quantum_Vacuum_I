"""Decimal arithmetic for the constants calculator, without binary-float seeds.

SymPy supplies pi (it is already a calculator dependency). Decimal supplies
sqrt, ln and exp at the active context precision. These are numerical results,
not certified intervals; Lean supplies the independent mathematical bounds.
"""

from decimal import Decimal, getcontext, localcontext
from functools import lru_cache


def decimal(value):
    """Convert exact literals/numbers, preserving their decimal representation.

    Float inputs are accepted for measured reference values at their existing
    published precision. This cannot recover digits previously lost to a float.
    Theory formulas should use integers, strings, Decimal or exact SymPy input.
    """
    if isinstance(value, Decimal):
        return value
    if hasattr(value, "evalf"):
        with localcontext() as ctx:
            ctx.prec += 12
            return +Decimal(str(value.evalf(ctx.prec)))
    return Decimal(str(value))


def configure(digits=5000):
    if not isinstance(digits, int) or digits < 30:
        raise ValueError("precision must be an integer of at least 30 digits")
    getcontext().prec = digits


@lru_cache(maxsize=8)
def _pi(digits):
    from sympy import pi as symbolic_pi

    with localcontext() as ctx:
        ctx.prec = digits + 20
        value = Decimal(str(symbolic_pi.evalf(ctx.prec)))
    with localcontext() as ctx:
        ctx.prec = digits
        return +value


def pi():
    return _pi(getcontext().prec)


def sqrt(value):
    return decimal(value).sqrt()


def log(value):
    return decimal(value).ln()


def exp(value):
    return decimal(value).exp()
