#!/usr/bin/env python3
"""Unit tests for tools/inline_bytes.py"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from inline_bytes import rewrite_text  # noqa: E402


BODY = ('(0 <= 0 && 0 <= len(s) && len(s) <= cap(s) && '
        'forall i int :: { &s[i] } 0 <= i && i < len(s) ==> acc(&s[i]))')

BODY_R10 = ('(0 <= 0 && 0 <= len(s) && len(s) <= cap(s) && '
            'forall i int :: { &s[i] } 0 <= i && i < len(s) ==> acc(&s[i], R10))')

BODY_WILD = ('(0 <= 0 && 0 <= len(s) && len(s) <= cap(s) && '
             'forall i int :: { &s[i] } 0 <= i && i < len(s) ==> acc(&s[i], _))')


class GobraTests(unittest.TestCase):

    def rewrite(self, s, specs_only=False, allow_bare=False):
        return rewrite_text(s, 'gobra', specs_only=specs_only,
                            allow_bare=allow_bare)

    def test_plain(self):
        src = 'requires sl.Bytes(s, 0, len(s))\n'
        self.assertEqual(self.rewrite(src), f'requires {BODY}\n')

    def test_with_fraction(self):
        src = 'requires acc(sl.Bytes(s, 0, len(s)), R10)\n'
        self.assertEqual(self.rewrite(src), f'requires {BODY_R10}\n')

    def test_wildcard(self):
        src = 'requires acc(sl.Bytes(s, 0, len(s)), _)\n'
        self.assertEqual(self.rewrite(src), f'requires {BODY_WILD}\n')

    def test_unfolding_in(self):
        src = 'pure func f() byte { return unfolding sl.Bytes(s, 0, len(s)) in s[0] }\n'
        out = self.rewrite(src)
        self.assertIn('return s[0]', out)
        self.assertNotIn('Bytes', out)

    def test_unfolding_acc_in(self):
        src = 'foo := unfolding acc(sl.Bytes(s, 0, len(s)), _) in s[0]\n'
        out = self.rewrite(src)
        self.assertIn(':= s[0]', out)
        self.assertNotIn('Bytes', out)

    def test_fold_line(self):
        src = 'a := 1\nfold sl.Bytes(s, 0, n)\nb := 2\n'
        self.assertEqual(self.rewrite(src), 'a := 1\nb := 2\n')

    def test_unfold_line(self):
        src = 'a := 1\n\tunfold acc(sl.Bytes(s, 0, n), R10)\nb := 2\n'
        self.assertEqual(self.rewrite(src), 'a := 1\nb := 2\n')

    def test_defer_fold_line(self):
        src = 'a := 1\n\tdefer fold sl.Bytes(s, 0, n)\nb := 2\n'
        self.assertEqual(self.rewrite(src), 'a := 1\nb := 2\n')

    def test_ghost_defer_fold_line(self):
        src = 'a := 1\n\tghost defer fold sl.Bytes(s, 0, n)\nb := 2\n'
        self.assertEqual(self.rewrite(src), 'a := 1\nb := 2\n')

    def test_ghost_defer_unfold_line(self):
        src = 'a := 1\n\tghost defer unfold acc(sl.Bytes(s, 0, n), R10)\nb := 2\n'
        self.assertEqual(self.rewrite(src), 'a := 1\nb := 2\n')

    def test_defer_unfold_in_go_annotation(self):
        src = 'pre\n\t// @ defer unfold sl.Bytes(s, 0, n)\npost\n'
        out = rewrite_text(src, 'go')
        self.assertNotIn('Bytes(', out)
        self.assertNotIn('unfold', out)
        self.assertIn('pre\n', out)
        self.assertIn('post\n', out)

    def test_slice_expr_arg(self):
        src = 'requires acc(sl.Bytes(s[a:b], 0, len(s[a:b])), R10)\n'
        out = self.rewrite(src)
        self.assertIn('&(s[a:b])[i]', out)
        self.assertIn('cap(s[a:b])', out)
        self.assertIn(', R10)', out)

    def test_helper_name_not_matched(self):
        src = 'sl.SplitRange_Bytes(s, 0, n, R10)\n'
        self.assertEqual(self.rewrite(src), src)

    def test_bare_bytes_default_ignored(self):
        src = 'requires Bytes(s, 0, n)\n'
        # Without allow_bare, leave alone.
        self.assertEqual(self.rewrite(src, allow_bare=False), src)

    def test_bare_bytes_with_flag(self):
        src = 'requires Bytes(s, 0, n)\n'
        out = self.rewrite(src, allow_bare=True)
        self.assertNotIn('Bytes(', out)
        self.assertIn('forall i int', out)

    def test_string_literal_untouched(self):
        src = 'foo := "sl.Bytes(s, 0, n)"\n'
        self.assertEqual(self.rewrite(src), src)

    def test_line_comment_untouched(self):
        src = '// references sl.Bytes(s, 0, n) in docs\n'
        self.assertEqual(self.rewrite(src), src)

    def test_specs_only_skips_func_body(self):
        src = (
            'requires sl.Bytes(s, 0, n)\n'
            'func F(s []byte, n int) {\n'
            '\tfold sl.Bytes(s, 0, n)\n'
            '}\n'
        )
        out = self.rewrite(src, specs_only=True)
        # Spec line rewritten:
        self.assertIn('forall i int', out.splitlines()[0])
        # Body unchanged:
        self.assertIn('\tfold sl.Bytes(s, 0, n)\n', out)

    def test_multiline_requires(self):
        src = 'requires sl.Bytes(\n\ts, 0, len(s))\n'
        out = self.rewrite(src)
        self.assertNotIn('Bytes(', out)
        self.assertIn('forall i int', out)

    def test_slices_dot_bytes(self):
        src = 'requires slices.Bytes(h, 0, len(h))\n'
        out = self.rewrite(src)
        self.assertNotIn('slices.Bytes', out)
        self.assertIn('forall i int', out)

    def test_preserves_form(self):
        src = 'preserves sl.Bytes(s, 0, len(s))\n'
        out = self.rewrite(src)
        self.assertTrue(out.startswith('preserves ('))


class GoFileTests(unittest.TestCase):

    def rewrite(self, s):
        return rewrite_text(s, 'go')

    def test_line_annotation(self):
        src = '// @ preserves sl.Bytes(s, 0, len(s))\n'
        out = self.rewrite(src)
        self.assertIn('// @ preserves (', out)
        self.assertNotIn('Bytes(', out)

    def test_line_annotation_no_space(self):
        src = '//@ preserves sl.Bytes(s, 0, len(s))\n'
        out = self.rewrite(src)
        self.assertNotIn('Bytes(', out)

    def test_block_annotation(self):
        src = '/*@\nrequires sl.Bytes(s, 0, len(s))\n@*/\n'
        out = self.rewrite(src)
        self.assertNotIn('Bytes(', out)
        self.assertIn('forall i int', out)

    def test_plain_comment_untouched(self):
        src = '// regular: sl.Bytes(s, 0, n)\n'
        self.assertEqual(self.rewrite(src), src)

    def test_code_untouched(self):
        src = 'x := sl.Bytes(s, 0, n)\n'  # not in annotation; should not change
        self.assertEqual(self.rewrite(src), src)

    def test_fold_line_in_block_annotation(self):
        src = '/*@\nfold sl.Bytes(s, 0, n)\nother\n@*/\n'
        out = self.rewrite(src)
        self.assertIn('other\n', out)
        self.assertNotIn('Bytes(', out)

    def test_fold_line_in_line_annotation(self):
        src = 'pre\n\t// @ fold sl.Bytes(s, 0, n)\npost\n'
        out = self.rewrite(src)
        self.assertNotIn('Bytes(', out)
        self.assertIn('pre\n', out)
        self.assertIn('post\n', out)


if __name__ == '__main__':
    unittest.main()
