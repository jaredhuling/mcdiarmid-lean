"""Failure-path tests for the evidence parser and reviewed-statement gate."""
import copy
import json
import unittest

from verify import check_review, parse_records, signature_hash


class VerificationFailures(unittest.TestCase):
    def setUp(self):
        self.record = {"declaration": "T", "elaborated_type": "True", "binders": [],
                       "axioms": ["propext"]}
        self.log = "AUDIT_DECLARATION " + json.dumps(self.record)
        self.review = {"declarations": {"T": {
            "signature_sha256": signature_hash(self.record), "proposition_binders": {}}},
            "definition_context_sha256": {}}

    def test_clean_record(self):
        self.assertEqual(parse_records(self.log, ["T"]), [self.record])
        check_review([self.record], self.review)

    def test_missing_or_duplicate_record_rejected(self):
        for log in ["", self.log + "\n" + self.log]:
            with self.assertRaises(ValueError):
                parse_records(log, ["T"])

    def test_unexpected_axiom_rejected(self):
        for name in ["sorryAx", "Extra.axiom"]:
            record = dict(self.record, axioms=[name])
            with self.assertRaises(ValueError):
                parse_records("AUDIT_DECLARATION " + json.dumps(record), ["T"])

    def test_error_after_success_rejected(self):
        with self.assertRaises(ValueError):
            parse_records(self.log + "\nfile: error: later failure", ["T"])

    def test_changed_statement_rejected(self):
        with self.assertRaises(ValueError):
            check_review([dict(self.record, elaborated_type="False")], self.review)

    def test_unreviewed_premise_rejected(self):
        record = dict(self.record, binders=[{"index": 0, "is_proposition": True}])
        with self.assertRaises(ValueError):
            check_review([record], self.review)
        review = copy.deepcopy(self.review)
        review["declarations"]["T"]["proposition_binders"]["0"] = {"provenance": "unclassified"}
        with self.assertRaises(ValueError):
            check_review([record], review)


if __name__ == "__main__":
    unittest.main()
