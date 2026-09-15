"""Negative tests ensure the proof audit rejects missing proofs and trust leaks."""
import unittest
from verify import ALLOWED_AXIOMS, EXPECTED_NAMES, NEGATIVE_TESTS, check_axioms, check_no_sorry


def fixture():
    lines = [f"'{name}' depends on axioms: [{', '.join(sorted(ALLOWED_AXIOMS))}]"
             for name in sorted(EXPECTED_NAMES)]
    lines += ["negative certificate test passed"] * NEGATIVE_TESTS
    return "\n".join(lines)


class AuditTests(unittest.TestCase):
    def test_expected_trust(self):
        self.assertEqual(set(check_axioms(fixture())), EXPECTED_NAMES)

    def test_missing_result(self):
        with self.assertRaises(ValueError):
            check_axioms(fixture().split("\n", 1)[1])

    def test_sorry_rejected(self):
        with self.assertRaises(ValueError):
            check_axioms(fixture().replace("[", "[sorryAx, ", 1))

    def test_native_rejected_everywhere(self):
        for name in EXPECTED_NAMES:
            with self.subTest(name=name), self.assertRaises(ValueError):
                check_axioms(fixture().replace(
                    f"'{name}' depends on axioms: [",
                    f"'{name}' depends on axioms: [Lean.ofReduceBool, "))

    def test_missing_negative_test(self):
        with self.assertRaises(ValueError):
            check_axioms(fixture().replace("negative certificate test passed", "", 1))


class SorryTests(unittest.TestCase):
    def test_clean_build_accepted(self):
        check_no_sorry("✔ [10/10] Built Sz8.Galois.MainTheorem (12s)\nBuild completed successfully.")

    def test_sorry_rejected(self):
        with self.assertRaises(ValueError):
            check_no_sorry("warning: Sz8/Galois/MainTheorem.lean:12:8: declaration uses `sorry`")


if __name__ == "__main__":
    unittest.main()
