/-!
# Principal component error in high-dimensional factor models

Root module. Importing this file gives every result of Bernstein, Goldberg, Gunther,
Kercheval, Lan, Lin and Yao, *Principal component error in high-dimensional factor models*
(version of September 14, 2026).

See `PAPER-MAP.md` for the paper-result ↔ Lean-declaration index.
-/

-- Vocabulary, the paper's objects, Assumptions 1–6
import LatentError.Basic
import LatentError.Defs
import LatentError.Model

-- The paper's results
import LatentError.Statements.Appendix      -- Lemmas 1–6, Propositions 1–3, Corollaries 2–3
import LatentError.Statements.Main          -- Theorems 1–3, Corollary 1, eqs. (16), (20), (25)
import LatentError.Statements.Conditional   -- the joint → conditional-on-F links of §4

-- The three background facts, proved, and the headline results with them discharged
import LatentError.Facts.Unconditional

-- The hypothesis bundles are inhabited: no statement is vacuous
import LatentError.Lemmas.NonVacuity
