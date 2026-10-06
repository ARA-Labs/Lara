# Simformer original-output checking package

The two files under `evidence/` are complete, unchanged author repository files:

- Repository: https://github.com/mackelab/simformer
- Revision: `a35055613aaae7c84067416932e5636ef34b2ed2`
- Original CSV: https://raw.githubusercontent.com/mackelab/simformer/a35055613aaae7c84067416932e5636ef34b2ed2/results/example_guidance/summary.csv
- CSV bytes: 4397; SHA-256: `9274a5de460f391d6862f256433cb004c7d4356c7e43b34f447f4bcdd5d09297`
- Original notebook: https://raw.githubusercontent.com/mackelab/simformer/a35055613aaae7c84067416932e5636ef34b2ed2/example/1_minimal_code_example.ipynb
- Notebook bytes: 286082; SHA-256: `3e0d0055bb4688f6753ccb3a14a313a666a883d3a2b38a3f2a04bc85865a9869`
- Authors: Manuel Gloeckler, Michael Deistler, Christian Weilbach, Frank Wood, Jakob H. Macke.

The original MIT license, Copyright (c) 2024 Manuel Gloeckler, is retained in `ORIGINAL-LICENSE`. The CSV's three unique model IDs select saved training runtimes, not its empty metric results. Notebook cell 19 prints the mean accumulated denoising loss for each block of 5000 updates. Its first five saved output strings end in exactly one LF; the explicit `decimal-line` encoding decodes that producer format. These five positions are from the same run, not five independent experiments or paper accuracy results.

`PAPER.md` is an unchanged reconstruction from `artifacts/paperbench/all-in-one/PAPER.md` in https://github.com/AmberLJC/ara-paperbench at `62e9b54b2d4efe45b97f25676a16784530dd552a`. Copyright (c) 2026 Amber Liu and the ARA project contributors; its CC BY 4.0 terms are retained in `PAPER-LICENSE`. This notice does not relicense the author's original CSV or notebook.

The Lara source assertions, policy and checking manifest are newly authored in Lara. The checking profile pins the accompanying paper, source, policy and requested evidence; it does not claim to validate the entire upstream ARA schema. Replay proves exact extraction from these packaged bytes, not the scientific interpretation or validity of the experiment. This package's own policy is self-approval unless a verifier supplies `--policy`.
