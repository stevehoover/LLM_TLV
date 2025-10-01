# What To Do When Full FEV Fails

If `fev.sh` fails for a fev_full* run, you must get the full FEV run to pass before making further changes to `wip.tlv`. In fact, `wip.tlv` is made read-only to discourage this, until full FEV passes.

When full FEV fails, the incremental run already succeeded, so the refactoring should be valid. Presumably something went wrong in the automation for updating `fev_full*.eqy`'s `[match ...]` section. The output of `fev.sh` should report internal signals for the non-passing partitions that may indicate missing/flawed match lines. You may safely modify the `fev_full*.eqy` match sections directly to fix issues, and rerun `fev.sh`. `fev.sh` should recognize that incremental FEV completed successfully already, and repeat full FEV runs. If there are issues with the idempotence of `fev.sh`, read its header comments for additional insight.

As you resolve the issue it will be helpful if you can identify what went wrong and report on the issue in `tracker.md`, so the user can improve the automation or instructions. Some background on the automation details may be helpful for this.

`fev_full*.eqy` files should contain a full match list for all signals in `prepared.sv`. `fev.eqy` should contain only those signals/pipesignals that differ between `feved.tlv` and `wip.tlv`.

`fev.sh` involves three idempotent substeps:

- Incremental FEV
- Update fev_full Matches
- Full FEV

The "Incremental FEV" substep extracts the WIP name changes from `fev.eqy` into `match_lines.eqy`. The "Update fev_full Matches" substep uses the `update_full_match.py` script to incorporate these name changes into `fev_full*.eqy`. It empties `match_lines.eqy` on success, having fully incorporated the name changes. (If/when "Full FEV" passes, `match_lines.eqy` is deleted, indicating the completion of the refactoring step.)

"Full FEV" performs all full FEV runs. Before each run, it translate pipesignal paths to Verilog signal paths (using SandPiper). It runs FEV with `fev_full.eqy` first, which uses default parameters, like incremental FEV. It then runs FEV with `fev_full_*.eqy`, which have non-default parameter values. If the former passes, and a latter run fails, there may again be a match issue, but there is also the possibility of a logic issue specific to the non-default parameter vlaues. `wip.tlv` may be edited only to address parameter-specific logic bugs identified in the model. Rerunning FEV will produce a harmless warning and rerun all substeps.

For pipesignals, use the TL-Verilog pipesignal reference syntax in the match lines. These are translated to Verilog signal paths using SandPiper before running FEV (in "incremental FEV" for incremental FEV and in "Update fev_full Matches" for full FEV runs). (You may use the generated Verilog names in times of desperation, but inconsistency can affect subsequent full FEV match updates.)

In case you need to debug automation issues, two helper scripts are involved:

- `update_full_match.py`: Updates `fev_full*.eqy` to incorporate `match_lines.eqy`.
- `map_match_pipesignals`: Maps pipesignal paths to signal paths using SandPiper. Produces `tmp/latest/match/XXX.eqy` from `XXX.eqy`.

The following Intermediate files from these scripts are written to `tmp/latest/match/`. (`latest` is a symlink, updated by each `fev.sh` run.):

for incremental FEV:
- `match_lines.eqy`: extracted from `fev.eqy`'s `[match ...]` section.
- `fev.eqy.upd`: `fev.eqy` with `[match ...]` section removed.

for full FEV:
- `fev_full*.eqy.upd`: `fev.eqy` with `[match ...]` section updated to reflect `match_lines.eqy`.

for both:
- `fev*_match.tlv`: `wip.tlv` with an `\SV_plus` section appended for translating pipesignal references.
- `fev*_match.sv`: generated from `fev_full*_match.tlv` to contain pure Verilog match section lines.
- `fev*.eqy`: corresponding to the working `../../fev*.eqy` files, with pipesignals mapped to signals, provided to `eqy` command.
