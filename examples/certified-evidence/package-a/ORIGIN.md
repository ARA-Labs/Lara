# CompoNet original-output checking package

`evidence/benchmarking.csv` is the complete, unchanged `data/benchmarking.csv` member of the original author archive:

- Repository: https://github.com/mikelma/componet
- Revision: `7257a17e9dbb50f81482da65cdae2086c761aaa2`
- Archive: https://raw.githubusercontent.com/mikelma/componet/7257a17e9dbb50f81482da65cdae2086c761aaa2/experiments/meta-world/data.tar.xz
- Archive bytes: 4918964; SHA-256: `4d91703cf10953b4f38818234eea57c2588ab58159943dc4885df1e36bca1059`
- Complete CSV bytes: 298568; SHA-256: `d346381c8af21c6b51440a181af3bf475edca0ce63c5e95362845a23a30261f6`
- Authors: Mikel Malagón, Josu Ceberio, Jose A. Lozano.

The original GPLv3 license is retained in `ORIGINAL-LICENSE`. The unchanged producer `experiments/meta-world/benchmarking.py` is retained as `origin/benchmarking.py`; it writes benchmark measurement times and labels their unit as seconds. The selected rows are recorded trials of ProgressiveNet, not a comparison claiming CompoNet's superiority. The original empty CSV index header is intentional. Trial indices 1631 and 1632 each identify exactly one original row.

`PAPER.md` is an unchanged reconstruction from `artifacts/paperbench/self-composing-policies/PAPER.md` in https://github.com/AmberLJC/ara-paperbench at `62e9b54b2d4efe45b97f25676a16784530dd552a`. Copyright (c) 2026 Amber Liu and the ARA project contributors; its CC BY 4.0 terms are retained in `PAPER-LICENSE`. This notice does not relicense the author's original CSV or code.

The Lara source assertions, policy and checking manifest are newly authored in Lara. The checking profile pins the accompanying paper, source, policy and requested evidence; it does not claim to validate the entire upstream ARA schema. Replay proves exact extraction from these packaged bytes, not the scientific interpretation or validity of the experiment. This package's own policy is self-approval unless a verifier supplies `--policy`.
