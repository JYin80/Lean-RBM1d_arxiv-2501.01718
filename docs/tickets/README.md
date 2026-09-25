# Ticket specifications (written by the dispatcher; never edited after release — corrections go in T####-amend-N.md)

Template for `docs/tickets/T####.md`:

```text
Ticket: T####
Group / type: <group id> / prove | audit | repair
Role: prover | prover-hard | repairer   (audit stage always uses: auditor)
Release condition for the audit stage: <e.g. prove report shows math preflight PASS; modules X,Y build>
Math source and targets: <one line per target: paper formula / page, exact Lean declaration name and statement sketch>
Step 0 (read-only checks the dispatcher could not verify): <item; if false, compile the negation and stop>
Dependencies (must already be accepted): <declarations / tickets>
Upstream / downstream: <...>; why high vs xhigh: <...>
Sole writable files: <paths>        Must not touch: <paths>
Root import: <none | the hub adds `import RBM1D.X` at merge time>
Branch: t/T####
Required reading (only these): <CLAUDE.md sections, reports, source files>
Acceptance criteria: <per target>
```
