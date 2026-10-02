import unittest

from verify_lean_axioms import AuditError, verify


class VerifyLeanAxiomsTest(unittest.TestCase):
    driver = "import Example\n#print axioms Example.first\n#print axioms Example.second\n"
    valid = ("'Example.first' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
             "'Example.second' does not depend on any axioms\n")

    def test_allowed_axioms_and_axiom_free_declaration(self):
        self.assertEqual(verify(self.driver, self.valid, 2), 2)

    def test_wrapped_report_and_crlf(self):
        wrapped = self.valid.replace("Classical.choice, ", "Classical.choice,\n  ")
        self.assertEqual(verify(self.driver.replace("\n", "\r\n"), wrapped, 2), 2)

    def test_rejects_every_nonstandard_axiom(self):
        for axiom in ("sorryAx", "Lean.trustCompiler", "Lean.ofReduceBool", "Example.oracle"):
            with self.subTest(axiom=axiom), self.assertRaises(AuditError):
                verify(self.driver, self.valid.replace("propext", axiom), 2)

    def test_rejects_missing_extra_and_duplicate_reports(self):
        for log in ("", self.valid.splitlines()[0],
                    self.valid + "'Example.extra' depends on axioms: []\n",
                    self.valid + self.valid.splitlines()[0]):
            with self.subTest(log=log), self.assertRaises(AuditError):
                verify(self.driver, log, 2)

    def test_rejects_diagnostics_and_malformed_lists(self):
        for log in ("error: unknown identifier\n" + self.valid,
                    self.valid + "warning: declaration uses 'sorry'\n",
                    self.valid.replace("Quot.sound]", "Quot.sound,]"),
                    self.valid.replace("axioms:", "axiom:")):
            with self.subTest(log=log), self.assertRaises(AuditError):
                verify(self.driver, log, 2)

    def test_rejects_empty_duplicate_and_truncated_drivers(self):
        for driver in ("import Example\n", self.driver + "#print axioms Example.first\n",
                       "#print axioms Example.first\n", self.driver + "#print axioms\n"):
            with self.subTest(driver=driver), self.assertRaises(AuditError):
                verify(driver, self.valid, 2)


if __name__ == "__main__":
    unittest.main()
