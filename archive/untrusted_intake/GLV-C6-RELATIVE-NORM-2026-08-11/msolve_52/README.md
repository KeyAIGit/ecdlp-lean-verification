# Permanent msolve 52-system evidence

This directory is the permanent repository copy of the bounded F4/DRL comparison recorded in `../msolve_52_bounded_result.md`.

It preserves both positive and negative information:

- the direct `q_c6_orbit` representation won the tested F4 matrix comparisons for every `k >= 2` fixture;
- it paid a startup penalty at `k = 1`;
- the run establishes no asymptotic exponent change and no secp256k1 discrete-log recovery;
- the full raw shard logs, aggregate tables, exact provenance and cryptographic hashes are retained so later work can replay or contradict this result without losing history.

Files:

- `combined_summary.json` and `.csv`: all 52 normalized outcomes;
- `RESULTS_RAW.md`: aggregator output from the completed workflow;
- `raw_shards.tar.gz`: every per-system stdout, timing record, exit code and extracted metric line;
- `glv-msolve-all-52.zip`: byte-identical GitHub Actions artifact;
- `provenance.json`: frozen execution identity and scope boundary;
- `SHA256SUMS`: hashes of every retained file.

The data remain quarantined under `archive/untrusted_intake/`. They are evidence for review, not an authorized Research Engine outcome.
