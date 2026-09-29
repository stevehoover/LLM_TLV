# Converting Verilog to TL-Verilog Using Desktop Coding Agents

## Overview

This directory contains the necessary files to convert Verilog to TL-Verilog using a desktop coding agent like Claude Code.

You'll work with an LLM "setup agent", which might be Claude Code or GitHub Copilot, to set up the project for conversion, defining the process that will be followed and creating the directory structure for the work.

After initial setup, conversion will be completed by Claude Code "conversion agents". These run in a Docker sandbox with limited access, though not complete isolation. They have internet access (needed for SandPiper-SaaS only).

Conversion will use formal equivalence verification to ensure correctness. To preserve the verification environment, the setup agent can also establish a regression process using the project's established testing methodology, and the "conversion agents" can update verification collateral throughout the conversion.

If/when conversion is completed successfully, there will be collateral (in `fev*.eqy`) that defines the mapping of original Verilog signals to Verilog signals generated from TL-Verilog that can be used to make any remaining corrections in the environment. There will also be a report, `tracker.md`, for each converted module, containing considerations for review.

## (Human) Setup

Create a local clone of a Verilog project's Git repository. In the project's top-level directory (probably the top-level directory of the repository), run:

```sh
cd <PROJECT-ROOT>
<PATH-TO>/desktop_agent_verilog_conversion/conversion_setup/setup.sh
```

This creates:
./tlv/
   env/          # Docker environment files
      Dockerfile  # Read-only, baseline Dockerfile for code conversion
      docker-compose.yml   # Seeded to use Dockerfile, for project-specific configuration
      settings.local.json  # for Claude configuration
      claude-config.json   # for Claude configuration
      install_verilator    # Verilator installation script
   project_instructions/   # Setup agent instructions
      project_setup_instructions.md
   regress/      # Empty directory for regression testing setup

The conversion agents are instructed to make changes only within `tlv/`, but they will have full access to <PROJECT_ROOT> so they are able to run project regressions.

## (LLM) Setup

Use a coding agent to follow `tlv/project_instructions/project_setup_instructions.md`, informing the agent of any additional instructions, which must include:

- whether the agent should get the project's environment working on the local machine
- whether the agent should establish regression testing using the project's environment

For example, in GitHub Copilot, open a workspace containing the project root directory, and provide the Copilot agent with this prompt:

 Follow instructions in `tlv/project_instructions/project_setup_instructions.md` to prepare for conversion of the Verilog project source code to TL-Verilog. Get the project's environment working locally and in the Docker conversion environment, establishing a regression testing flow for conversion agents.

The agent should produce:

- `tlv/env/docker-compose.yml`: a Docker environment for the conversion, including the project's environment for regression testing
- `tlv/project_instructions/project_specific_instructions.md`: project-specific instructions for conversion agents
- `tlv/regress/regress.sh` (or similar): a script for conversion agents to run to regress changes using the project's environment, referenced by `project_specific_instructions.md`.

## Local Checks Before SandPiper

`scripts/fev.sh` runs two mechanical checks in the module directory before it calls SandPiper-SaaS, so whole classes of errors are reported locally in milliseconds rather than after a cloud round trip.

`scripts/tlv_lint.py --strict .` checks `wip.tlv` and the `[match ...]` sections of every `fev*.eqy` against the TL-Verilog spec and the Macros Guide: identifier form (`/x`, `|p`, `$FOO`, a state signal `$Foo` assigned without `<=` or an alignment), a non-comment line at column 0 that ends a `\TLV` region, indentation that is not a multiple of three or uses tabs, a reference whose first path element is a sibling scope rather than an ancestor or child (`/serv_rf_ram_if|default$x` written from inside `/top|default`), duplicate scope names along one path, an alignment (`<>0`, `>>N`, `<<N`) that is not at the end of the path, and M5 argument hygiene (unbalanced `['` `']`, a multi-line `m5+` call whose continuation is not indented past the call, `//` inside an argument list). Each finding is one line, `file:line: RULE: message (spec section)`; fev.sh fails with status 2 and sends nothing to SandPiper. The rule set was checked against sandpiper-saas 1.14 and lints the proven serv conversions, the Makerchip tutorial and example corpora, and warp-v clean. `--strict` adds the spec's two-letter minimum for `$` names (`$a` must be `$aa`), which SandPiper does not enforce. `scripts/tlv_lint_test.py` holds the synthetic cases for every rule.

`scripts/config_coverage.py .` reads the parameters declared in `orig.sv` and the `chparam -set` lines of every `fev_full*.eqy`, and reports per parameter whether any FEV configuration changes it from its default (a parameter derived from another, such as `B = W-1`, is reported as derived). It exits 1 when at least one parameter is never varied. fev.sh runs it with `--warn-only` and prints its warnings without failing, since some parameters are legitimately fixed for a conversion.

## Docker Environment

`tlv/env/Dockerfile` defines an image with all TL-Verilog conversion tools pre-installed. The setup agent may customize this by creating project-specific extensions via `tlv/env/Dockerfile.project` and `tlv/env/docker-compose.yml`.

### Build and Run

From `tlv/env/`:

```bash
docker compose up claude-conversion   # To run Claude Code interactively
docker compose run --rm claude-conversion bash   # Shell access for debugging
```
