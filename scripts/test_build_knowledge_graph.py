#!/usr/bin/env python3
"""Cross-platform determinism fixtures for the knowledge-graph generator."""

from __future__ import annotations

import unittest
from pathlib import PurePosixPath, PureWindowsPath

from build_knowledge_graph import classify_area, stable_repo_path


class KnowledgeGraphDeterminismTests(unittest.TestCase):
    def test_module_order_is_identical_across_path_flavors(self) -> None:
        relative = [
            "Ecdlp/Proved/Secp256k1Params.lean",
            "Ecdlp/Proved/Secp256k1PMinusOneSmoothness.lean",
            "Ecdlp/Proved/Secp256k1PrimeP.lean",
        ]
        windows_root = PureWindowsPath("C:/repo")
        posix_root = PurePosixPath("/repo")
        windows = [windows_root / item for item in relative]
        posix = [posix_root / item for item in relative]

        windows_order = [
            stable_repo_path(path, windows_root)
            for path in sorted(
                windows,
                key=lambda path: stable_repo_path(path, windows_root),
            )
        ]
        posix_order = [
            stable_repo_path(path, posix_root)
            for path in sorted(
                posix,
                key=lambda path: stable_repo_path(path, posix_root),
            )
        ]

        self.assertEqual(posix_order, windows_order)
        self.assertEqual(
            [
                "Ecdlp/Proved/Secp256k1PMinusOneSmoothness.lean",
                "Ecdlp/Proved/Secp256k1Params.lean",
                "Ecdlp/Proved/Secp256k1PrimeP.lean",
            ],
            windows_order,
        )


class AreaClassificationTests(unittest.TestCase):
    def test_parity_rows_are_not_filed_under_primality(self) -> None:
        # The parity / Fourier rows mention "prime n"; the bit-security rule
        # must win over the primality rule, by claim text or by module path.
        self.assertEqual(
            "bit-security",
            classify_area(
                "Balance identity of `J` (prime `n ≠ 2`, ...)",
                "Ecdlp.Proved.ParityFourier.ProofsF2",
            ),
        )
        self.assertEqual(
            "bit-security",
            classify_area("An exact parity oracle recovers the logarithm by halving", ""),
        )

    def test_primality_rows_keep_their_area(self) -> None:
        self.assertEqual(
            "primality",
            classify_area("`p` is prime (Pratt certificate)", "Ecdlp.Proved.Secp256k1PrimeP"),
        )


if __name__ == "__main__":
    unittest.main()
