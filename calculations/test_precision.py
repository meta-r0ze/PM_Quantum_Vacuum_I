"""Run with: python3 -m unittest test_precision.py

Numerical regressions complement, and do not replace, the Lean proofs.
"""
import ast
import contextlib
from decimal import Decimal, getcontext, localcontext
import inspect
import io
import re
import unittest

import constants
from high_precision import configure, pi
from output_helpers import to_latex_sci, to_latex_sci_with_err


class PrecisionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.runs = {}
        for digits in (70, 110):
            with contextlib.redirect_stdout(io.StringIO()):
                cls.runs[digits] = constants.main(['--paper', '3', '--digits', str(digits)])

    def test_no_float_literals_or_math_calls_seed_main(self):
        tree = ast.parse(inspect.getsource(constants.main))
        for node in ast.walk(tree):
            self.assertFalse(isinstance(node, ast.Constant) and isinstance(node.value, float))
            if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
                self.assertNotEqual(node.value.id, 'math')

    def test_results_stable_as_precision_increases(self):
        low, high = self.runs[70], self.runs[110]
        self.assertEqual(low.keys(), high.keys())
        for name in low:
            self.assertIsInstance(high[name], Decimal, name)
            scale = max(abs(high[name]), Decimal('1e-200'))
            self.assertLess(abs(low[name] - high[name]) / scale, Decimal('1e-65'), name)

    def test_paper_one_certified_enclosure(self):
        value = self.runs[110]['AlphaInv']
        self.assertGreater(value, Decimal('137.035999212381397211'))
        self.assertLess(value, Decimal('137.035999212381397213'))
        self.assertTrue(str(value).startswith('137.0359992123813972118735343515923459915642878144'))

    def test_exact_rational_scalar(self):
        with localcontext() as ctx:
            ctx.prec = 110
            self.assertEqual(self.runs[110]['HiggsLambda'], Decimal(128) / 989)

    def test_wavelength_unit_conversion(self):
        with localcontext() as ctx:
            ctx.prec = 110
            values = self.runs[110]
            expected = 2 * pi() * Decimal('197.327') * Decimal('1e-9')
            actual = values['WavelengthMicrometers'] * values['FloorMassMeV']
            self.assertLess(abs(actual - expected), Decimal('1e-100'))

    def test_joint_model_matches_lean_enclosures(self):
        values = self.runs[110]
        bounds = {
            'WMassFromResponse': ('78.96', '78.97'),
            'ZMassFromResponse': ('89.57', '89.58'),
            'HiggsMass': ('125.2692637', '125.2692639'),
            'FermiConst': ('0.00001166378', '0.00001166380'),
            'ElectronClosureRatio': ('0.99972687', '0.99972689'),
            'SurfaceReflectionFraction': ('0.000000001', '0.00000001'),
            'StrongCouplingSquared': ('1.4816', '1.4817'),
            'ElectronClosureCoefficient': ('1.28777', '1.28779'),
            'InterfaceFactor': ('1.0362', '1.0365'),
            'AntiscreeningRequired': ('0.0236', '0.0242'),
            'AlphaSTauThreshold': ('0.27', '0.29'),
        }
        for name, (lower, upper) in bounds.items():
            self.assertGreater(values[name], Decimal(lower), name)
            self.assertLess(values[name], Decimal(upper), name)

    def test_closure_defined_yukawa(self):
        values = self.runs[110]
        self.assertGreater(values['StrongAtInterfaceFactor'], Decimal('0.1221'))
        self.assertGreater(values['ZpoleFactor'], Decimal('1.07'))
        self.assertLess(values['ElectronYukawaSigmaD'], values['ElectronYukawa'])

    def test_measured_z_validation_is_separate(self):
        values = self.runs[110]
        self.assertGreater(values['WMassFromMeasuredZ'], Decimal('80'))
        self.assertLess(values['WMassFromResponse'], Decimal('79'))
        self.assertNotEqual(values['ZMassFromResponse'], constants.REFS['mz'].value)

    def test_small_and_large_decimal_formatting(self):
        self.assertIn('10^{-10000}', to_latex_sci(Decimal('1e-10000')))
        self.assertIn('10^{10000}', to_latex_sci(Decimal('1e10000')))
        self.assertIn('10^{-10000}', to_latex_sci_with_err(Decimal('1e-10000'), Decimal('2e-10002')))
        self.assertNotEqual(constants.format_latex_tag(Decimal('1.99999999999999999999'), 20), '2')

    def test_pi_precision_is_configurable(self):
        configure(80)
        self.assertTrue(str(pi()).startswith('3.14159265358979323846264338327950288419716939937510'))
        configure(120)
        self.assertGreater(len(pi().as_tuple().digits), 100)

    def test_both_latex_cli_paths(self):
        for paper in ('1', '3'):
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                constants.main(['--paper', paper, '--digits', '60', '--latex'])
            text = output.getvalue()
            tags = re.findall(r'%<\*([^>]+)>[^\n]*?%</([^>]+)>', text)
            self.assertTrue(tags)
            self.assertTrue(all(a == b for a, b in tags), [(a, b) for a, b in tags if a != b])

    def test_invalid_precision_rejected(self):
        with self.assertRaises(ValueError):
            configure(20)


if __name__ == '__main__':
    unittest.main()
