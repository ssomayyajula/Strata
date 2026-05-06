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
1. Write a PLAN: what will change, which file/lines, why (cite architecture)
2. The plan is reviewed against the architecture
3. Only THEN execute

If I find myself writing code without a plan that traces to the architecture,
I am doing it wrong. If an agent writes code without stating its plan first,
it is doing it wrong. Kill it.

## The Review Agent

- Reads both docs (ARCHITECTURE.md + IMPLEMENTATION_PLAN.md)
- Reads .claude/agent-preamble.md
- Runs ALL compliance checks
- Reports violations
- Does NOT fix anything

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
