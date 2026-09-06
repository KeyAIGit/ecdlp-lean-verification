#!/usr/bin/env python3
"""Defensive regression fixtures; no real proof forgery or live target execution."""
from __future__ import annotations
import copy
import json
from pathlib import Path
import tempfile
import unittest
from check_axioms import AuditError, audit, is_native_decide, load_registry, main, parse_audit_output

NAME = "Fixture.statement"
LOG = f"'{NAME}' depends on axioms: [propext, Classical.choice]\n"

def registry(base: str = "standard") -> dict:
    return {"ledger_declarations": [NAME], "declarations": {NAME: {}}, "axiom_base": {NAME: base}}

class AuditTests(unittest.TestCase):
    def test_standard(self):
        self.assertEqual(audit(LOG, registry())["audited_declarations"], 1)
    def test_apostrophe_and_unicode(self):
        name = "Fixture.preΨ'_odd"
        blocks, free = parse_audit_output(f"'{name}' depends on axioms: [propext,\n Classical.choice]\n")
        self.assertEqual(blocks, [(name, "propext,\n Classical.choice")]); self.assertEqual(free, [])
    def test_axiom_free_apostrophe(self):
        self.assertEqual(parse_audit_output("'Fixture.example'' does not depend on any axioms\n"), ([], ["Fixture.example'"]))
    def test_empty_axiom_list(self):
        self.assertEqual(audit(f"'{NAME}' depends on axioms: []\n", registry())["compiler_trusted"], [])
    def test_crlf(self):
        self.assertEqual(audit(LOG.replace('\n', '\r\n'), registry())["audited_declarations"], 1)
    def test_warning_not_record(self):
        self.assertEqual(audit("file.lean:1:0: warning: unused variable\n"+LOG, registry())["audited_declarations"], 1)
    def test_empty_log(self):
        with self.assertRaises(AuditError): audit("", registry())
    def test_duplicate_record(self):
        with self.assertRaises(AuditError): audit(LOG+LOG, registry())
    def test_conflicting_record_forms(self):
        with self.assertRaises(AuditError): audit(LOG+f"'{NAME}' does not depend on any axioms\n", registry())
    def test_truncated_additional_record(self):
        with self.assertRaises(AuditError): audit(LOG+"'Fixture.other' depends on axioms: [propext\n", registry())
    def test_trailing_unparsed_record_suffix(self):
        with self.assertRaises(AuditError): audit(LOG.rstrip()+" trailing\n", registry())
    def test_elaboration_error(self):
        with self.assertRaises(AuditError): audit(LOG+"file.lean:2:0: error: invalid declaration\n", registry())
    def test_unknown_identifier(self):
        with self.assertRaises(AuditError): audit(LOG+"unknown identifier\n", registry())
    def test_terminal_control(self):
        with self.assertRaises(AuditError): audit("\x1b[0m"+LOG, registry())
    def test_null_control(self):
        with self.assertRaises(AuditError): audit(LOG+"\0", registry())
    def test_empty_registry(self):
        with self.assertRaises(AuditError): audit(LOG, {})
    def test_empty_ledger(self):
        r=registry(); r['ledger_declarations']=[]
        with self.assertRaises(AuditError): audit(LOG, r)
    def test_wrong_ledger_type(self):
        r=registry(); r['ledger_declarations']=NAME
        with self.assertRaises(AuditError): audit(LOG, r)
    def test_duplicate_ledger_name(self):
        r=registry(); r['ledger_declarations']=[NAME,NAME]
        with self.assertRaises(AuditError): audit(LOG, r)
    def test_unknown_observed_name(self):
        with self.assertRaises(AuditError): audit(LOG.replace(NAME,'Fixture.other'), registry())
    def test_missing_declarations(self):
        r=registry(); r['declarations']={}
        with self.assertRaises(AuditError): audit(LOG,r)
    def test_empty_present_base_map(self):
        r=registry(); r['axiom_base']={}
        with self.assertRaises(AuditError): audit(LOG,r)
    def test_invalid_base(self):
        with self.assertRaises(AuditError): audit(LOG,registry('unspecified'))
    def test_legacy_registry_is_explicit(self):
        r=registry(); del r['axiom_base']
        self.assertFalse(audit(LOG,r)['per_row_base_checked'])
    def test_missing_output(self):
        r=registry(); r['ledger_declarations'].append('Fixture.other'); r['declarations']['Fixture.other']={}; r['axiom_base']['Fixture.other']='standard'
        with self.assertRaises(AuditError): audit(LOG,r)
    def test_forbidden_sorry(self):
        with self.assertRaises(AuditError): audit(LOG.replace('propext','sorryAx'),registry())
    def test_forbidden_guard_messages(self):
        with self.assertRaises(AuditError): audit(LOG.replace('propext','Lean.guardMsgsAx'),registry())
    def test_unrecognized_dependency(self):
        with self.assertRaises(AuditError): audit(LOG.replace('propext','Fixture.unrecognized'),registry())
    def test_native_requires_declared_base(self):
        with self.assertRaises(AuditError): audit(LOG.replace('propext','Lean.ofReduceBool'),registry())
    def test_disclosed_compiler_trust(self):
        self.assertEqual(audit(LOG.replace('propext','Lean.trustCompiler'),registry('standard+native_decide'))['compiler_trusted'],[NAME])
    def test_native_aux_known_owner(self):
        text=LOG.replace('propext',NAME+'._native.native_decide.ax_1_2')
        self.assertEqual(audit(text,registry('standard+native_decide'))['compiler_trusted'],[NAME])
    def test_native_aux_unknown_owner(self):
        text=LOG.replace('propext','Fixture.other._native.native_decide.ax_1_2')
        with self.assertRaises(AuditError): audit(text,registry('standard+native_decide'))
    def test_native_aux_needs_registry(self):
        with self.assertRaises(AuditError): audit(LOG.replace('propext',NAME+'._native.native_decide.ax_1_2'))
    def test_native_format_is_closed(self):
        self.assertFalse(is_native_decide('Fixture.native_decide.ax'))
        self.assertFalse(is_native_decide('Fixture._native.native_decide.ax_unrecognized'))
    def test_empty_axiom_atom(self):
        with self.assertRaises(AuditError): audit(LOG.replace('propext,','propext,,'),registry())
    def test_duplicate_axiom(self):
        with self.assertRaises(AuditError): audit(LOG.replace('Classical.choice','propext'),registry())
    def test_duplicate_json_key(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'registry.json'; p.write_text('{"ledger_declarations":[],"ledger_declarations":[]}',encoding='utf-8')
            with self.assertRaises(AuditError): load_registry(p)
    def test_invalid_json_shape(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'registry.json'; p.write_text('[]',encoding='utf-8')
            with self.assertRaises(AuditError): load_registry(p)
    def test_cli_missing_file_fails_cleanly(self):
        self.assertEqual(main(['check_axioms.py','/nonexistent/axiom-log']),1)
    def test_cli_success(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d); (p/'log').write_text(LOG,encoding='utf-8'); (p/'registry').write_text(json.dumps(registry()),encoding='utf-8')
            self.assertEqual(main(['check_axioms.py',str(p/'log'),str(p/'registry')]),0)

if __name__ == '__main__':
    unittest.main(verbosity=2)
