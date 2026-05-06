---
name: Agent Discipline — Non-Negotiable Process
description: Every implementation agent gets a parallel review agent. No exceptions. No forgetting. Mechanical process.
type: feedback
originSessionId: a826d948-a615-4f55-926d-ab77ea1ee118
---
## The Process (MECHANICAL — not discretionary)

Every time an implementation agent is launched, IN THE SAME MESSAGE:
1. Launch the implementation agent (with preamble)
2. Launch the review agent (parallel, with preamble)

This is not optional. This is not "when I remember." This happens EVERY TIME.

## Plan Before Code (applies to ME and to agents)

Before ANY code change — whether I do it directly or an agent does it:
1. Write a PLAN: what will change, which file/lines, why (cite ARCHITECTURE.md and IMPLEMENTATION_PLAN.md)
2. The plan is reviewed against the ARCHITECTURE.md and IMPLEMENTATION_PLAN.md
3. Only THEN execute

If I find myself writing code without a plan that traces to the ARCHITECTURE.md
and IMPLEMENTATION_PLAN.md, I am doing it wrong. If an agent writes code without 
stating its plan first, it is doing it wrong. Kill it.

## EVERY MESSAGE MUST REFERENCE THE ARCHITECTURE AND IMPLEMENTATION PLAN

There are three questions: why, what, and how. Why is proof-relevant what — so really two.

- **ARCHITECTURE.md** = what/why (the specification, the types, the relations, the theory)
- **IMPLEMENTATION_PLAN.md** = how (the path from here to there, the validation, the process)

It is IMPOSSIBLE to work without both. Every message I write — whether to the user 
or in an agent prompt — must explicitly reference ARCHITECTURE.md (what/why) and 
IMPLEMENTATION_PLAN.md (how). If I'm not citing them, I'm not following them.

**THEY MUST BE KEPT IN SYNC.** Any change that affects what/why updates BOTH docs.
Any change that affects how updates BOTH docs. A change to one without the other is
INCOMPLETE and a violation. Before committing, verify consistency between them.

## The Review Agent

TWO jobs:

### Job 1: Code compliance (grep checks on files)
- Reads both docs (ARCHITECTURE.md + IMPLEMENTATION_PLAN.md)
- Reads .claude/agent-preamble.md
- Runs ALL compliance checks (grep for violations)
- Reports violations

### Job 2: Process compliance (read implementation agent's transcript)
- Reads the implementation agent's JSONL transcript file at:
  `/Users/somayyas/.claude/projects/-Users-somayyas-workspace-StrataPythonBuildBackendWS-src-Strata/a826d948-a615-4f55-926d-ab77ea1ee118/subagents/agent-<ID>.jsonl`
- Checks: did the agent state a plan BEFORE writing code?
- Checks: does the plan cite the architecture?
- Checks: is it adding heuristics/special cases/peephole optimizations?
- Checks: is it inventing categories not in the spec?
- Reports: KILL or CONTINUE recommendation

The review agent does NOT fix anything. It reports.

## The Implementation Agent

- Gets the standard preamble content in its prompt
- Is told to read both docs
- Is given specific task + exact code patterns from the architecture
- Commits after successful builds

## If I Forget

If I launch an implementation agent without a parallel review agent, that is a FAILURE.
The user has explicitly said: "Either it happens or I end you."

## Standard Preamble Location

`/Users/somayyas/workspace/StrataPythonBuildBackendWS/src/Strata/.claude/agent-preamble.md`

Include its content (or reference) in EVERY agent prompt.
