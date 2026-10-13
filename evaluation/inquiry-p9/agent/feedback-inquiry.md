## What `./lara-view check` reports

The checker feedback is the **public status view** (the full public status of
every accepted completion, or of each query at the `before` and `after`
endpoints of an impact document), followed by the complete **inquiry
diagnostics** for every request:

- `status-body`: every completion row, including rejected rows and their exact
  rejection reason, then total/accepted/rejected counts and whether the status
  is stable across the whole family.
- `audit-body`: for every completion, whether the submitted fixed witness passes
  its audit under the stated profile, then whether it passes in every row.
- `stability-body`: `(stability-result OBSERVABLE total accepted rejected
  whole-outcome-stable accepted-only-stable)`.
- `assumptions-body`: the catalog, then every *minimal* set of catalog literals
  that leaves a nonempty, rejection-free family in which the target holds, with
  surviving completions and the countercompletion exposed by deleting each
  literal.
- `impact-body`: per query `(query-impact QUERY BEFORE AFTER changed locality)`.
  `locality` true is a certificate that the edit cannot affect the query's
  grounded status (its relevant ancestry and acceptance are unchanged); false
  means no such certificate exists, which does not by itself mean the status
  changed.
