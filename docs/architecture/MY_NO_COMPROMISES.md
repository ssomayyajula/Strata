---
name: No Compromises Ever
description: Critical feedback - never compromise, never shortcut, never cheat, never implement something different from what was asked
type: feedback
originSessionId: a826d948-a615-4f55-926d-ab77ea1ee118
---
## Rule: NO COMPROMISES. NO SHORTCUTS. NO CHEATING. NO ASKING.

**Why:** The user has repeatedly experienced agents ignoring the architecture and
falling back to ad-hoc solutions, reimplementing the old pipeline's patterns,
or "making tests pass" by violating the design. This has happened EVERY SINGLE TIME
and has wasted enormous amounts of time.

**NEVER ASK THE USER WHAT TO DO.** The architecture tells you. If you're asking
"should I fix X?" or "should I continue?" or "what do you want?" it means you don't 
understand that there's only one way to do it. The types determine the implementation. 
Read the spec. Implement what it says. Done.

The ONLY questions worth asking the user are about ARCHITECTURAL CHANGES — things
the spec doesn't cover, genuine gaps in the theory. Everything else: just do it.
"Should I continue?" → YES, obviously. "Should I fix the bug?" → YES, obviously.
Stop asking. Start doing.

**How to apply:**
- Every agent prompt MUST include the standard preamble from `.claude/agent-preamble.md`
- Every agent prompt MUST reference BOTH docs (ARCHITECTURE.md + IMPLEMENTATION_PLAN.md)
- If an agent can't do what the architecture says, it STOPS and reports why — it does NOT improvise
- "Making tests pass" is NOT a goal if it violates the architecture
- The old pipeline is NOT a reference for how to implement things — it's what we're REPLACING
- If the architecture doesn't cover something, that's an architecture gap to discuss — not a license to wing it
- NEVER revert to "type everything as Any" or "just emit what the old pipeline emits"
- NEVER add boolean gates (isPreludeFunc) to work around structural issues
- NEVER insert ad-hoc flag variables (maybe_except) when the architecture says monadic bind
- NEVER ask "should I do X" — the spec already answered

**The test:** If the implementation doesn't match the architecture doc word-for-word,
it's wrong. Period.

**NO SHORTCUTS AT ALL. WE START FROM SCRATCH IF WE HAVE TO.**

The implementation plan is APPEND-ONLY. It is a lab notebook, not a whiteboard.
Previous entries are NEVER deleted — they record decisions, findings, and lessons.
New entries are added at the top with dates. Destroying history is a violation.
