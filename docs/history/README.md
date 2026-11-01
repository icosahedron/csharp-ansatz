# Design history

The conversations that shaped LeanSharp, oldest first.

| Date | Record | Summary |
|---|---|---|
| 2026-10-31 | [ChatGPT: "Recommend CSharp Frontend"](2026-10-31-chatgpt-recommend-csharp-frontend.md) | The original idea: use Roslyn to make C# a frontend to a Lean kernel ported via Ansatz. Covers CIC as the IR, independent kernel checking, modular verification with database calls as assumptions, and importing Mathlib through lean4export. |
| 2026-10-31 – 11-01 | [Claude Code session transcript](2026-10-31-claude-code-session-transcript.md) | The whole Claude Code session, verbatim apart from condensed tool calls: design, milestone 1 (terms, lean4export), milestone 2 (kernel), the full-Init check, the reproduction guide and milestone 3 (cross-checking with Lean, property tests). |
| 2026-10-31 | [Claude Code design session](2026-10-31-claude-design-session.md) | Checked the ChatGPT claims against the Ansatz source. Chose direction B (verify existing C#), a verification server, the name LeanSharp and Apache 2.0. Produced [`../design.md`](../design.md). |
