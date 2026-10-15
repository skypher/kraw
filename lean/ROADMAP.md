# Lean formalization: receipt and spine

Final-facing theorems: `Kraw.main_theorem` (paper Theorem 1.1),
`Kraw.Tur_ge_one` and `Kraw.Tur_le_center` (Corollary 1.2) in `Kraw/Main.lean`.
Source: manuscript Version 2.0.3.  Phase 1 (the spine below) formalized
Sections 2–6; Phase 2 extended the formalization to the whole paper, including
Proposition 1.3, indexed in `Kraw/Paper.lean`.

Acceptance check: `make lean` from the repository root. It builds `Kraw` and
requires `#print axioms` (in `CheckAxioms.lean`) to list only `propext`,
`Classical.choice` and `Quot.sound` for each of the 77 declarations indexed in
`Kraw/Paper.lean`.
**Status (2026-10-03): passed. No `sorry`, no extra axioms.**

## Spine (supplier → consumer)

| Lean statement | File | Paper source | Consumer | Proof by |
|---|---|---|---|---|
| `p_of_gt`, `p_zero`, `p_one`, `p_rec`, `p_refl`, `p_top`, `T_swap`, `no_consec_zero`, `Tur_refl`, `Tur_top` | `Basic.lean` | §2, (2.1), Lemma 2.1 | all | LEAN-A (mercury) |
| `qform`, `T_nonneg_bulk`, `T_center`, `T_top` | `QuadForm.lean` | Thms 3.1, 3.2 | Main, Flow, EvenQ, OddQ | main agent |
| `T_nonneg_flow` | `Flow.lean` | Thm 3.3 | Main | LEAN-D (jupiter) |
| `gap_x_pos`, `gap_hered`, `gap_strip` | `GapStrip.lean` | Cor 3.4, Lemmas 3.5–3.6 | EvenQ, OddQ | LEAN-B (venus) |
| `T_nonneg_gap_even` | `EvenQ.lean` | Thm 4.1 | Main | LEAN-E (saturn) |
| `T_odd_u1`, `T_nonneg_gap_odd` | `OddQ.lean`, `OddCert.lean` | Prop 5.1, Lemma 5.2, Thm 5.3 | Main | LEAN-C (mars); odd-`D` base switched to the paper's factorization by the main agent |
| `main_of_le`, `main_theorem`, `Tur_ge_one`, `Tur_le_center` | `Main.lean` | §6, Thm 1.1, Cor 1.2 | — | main agent |

## Agent task record

| Task | Agent | Model / effort | Thread | Dispatched | Returned | Outcome |
|---|---|---|---|---|---|---|
| LEAN-A Basic, QuadForm, Flow | luna_max_mercury | gpt-6-luna / max | 01a0fbe3-f4c6-7960-898c-2fa8c8c323fb | 10-02 17:13 | stopped 20:15 | Basic accepted; QuadForm superseded by main agent; Flow superseded by LEAN-D |
| LEAN-B GapStrip, EvenQ | luna_max_venus | gpt-6-luna / max | 01a0fbe3-f4de-70e3-aa3c-532d1a66428d | 10-02 17:13 | stopped 20:15 | GapStrip accepted; EvenQ superseded by LEAN-E |
| LEAN-C OddQ | luna_max_mars | gpt-6-luna / max | 01a0fbe3-f4e9-7bb3-b010-7ff2be011d90 | 10-02 17:13 | 20:01 | accepted |
| LEAN-D Flow (parallel) | luna_max_jupiter | gpt-6-luna / max | 01a0fc0a-a32d-78e0-b8f5-f01c6416a31f | 10-02 17:55 | 20:01 | accepted |
| LEAN-E EvenQ (parallel) | luna_max_saturn | gpt-6-luna / max | 01a0fc0a-a2be-7840-b06f-cc01604002dc | 10-02 17:55 | 20:10 | accepted |
| LEAN-F OddQ (parallel) | luna_max_neptune | gpt-6-luna / max | 01a0fc0a-a331-7023-a082-335bb2cf659e | 10-02 17:55 | stopped 20:15 | superseded by LEAN-C |
| REVIEW-1 paper referee (read-only) | luna_max_ceres | gpt-6-luna / max | 01a0fc1e-b26b-7711-85c3-4ee8ea582783 | 10-02 18:20 | 18:35 | three local proof-text defects fixed; base factorization adopted |

Accepted files were merged only after their frozen statements were compared
with the skeleton and scanned for `sorry`/`axiom`/`native_decide`, and after
the whole project built here against the proved dependencies.

## Phase 2 (2026-10-02/03): the whole paper — complete

Index: `Kraw/Paper.lean` names every numbered statement and displayed claim of the
paper (Version 2.0.3), 77 declarations. `CheckAxioms.lean` prints the axioms of each.
**Status (2026-10-03 03:10): `make lean` passes. No `sorry` in any file. Every index
declaration depends only on `propext`, `Classical.choice`, `Quot.sound` (two use only
`propext`, `Quot.sound`).**

| Paper claims | Lean file(s) | Proof by |
|---|---|---|
| §1.1 `p = K`, degree, generating function; orthogonality (supporting result for the §1.3 norms, not a paper claim) | `Krawtchouk.lean` | pluto |
| §1.1 example `(5,2)`, real-argument counterexample | `Examples.lean` | eris |
| §1.3 normalization claims | `Normalization.lean` | haumea |
| §§1–3 remaining claims (unimodality, (3.1)–(3.2), shifted-basis remark, Thm 3.2 exact, Cor 3.4, `(84,1,2)`) | `Remarks.lean` | makemake |
| §5 in paper notation (Prop 5.1, (5.1), Lemma 5.2 with real windows) | `OddPublic.lean` | vesta |
| Lemma 5.2 coefficient table (`O₁`–`O₄`) | `CertTable.lean`, `CertTableAux.lean` | hygiea (statement corrected to `w, v ≥ 0` after its counterexample at `w = −4`) |
| dual Jacobi–Trudi (two columns) | `SchurJT.lean` | hebe (iris stopped, superseded) |
| Prop 1.3: `Tur = s_{(2^s)}(z)`, complement identity, symmetry | `SchurProp.lean` | flora |
| Prop 1.3: irreducible polynomial `GL_D(ℂ)` character | `GLRep` (pallas), `GLKernel` (main agent: coordinate model), `GLEquiv`+`GLEquivAux` (pallas), `GLSurj`+`GLSurjAux` (europa), `GLTrace` (io), `GLPoly` (ganymede), `GLStdMono` (nereid: count; triton: independence; spliced by main agent), `GLCyclic` (callisto), `GLIrred` (titan), `GLChar` (main agent: assembly) | as listed |
| §1.2 character values positive, symmetric, unimodal; Schur sign remark; cell parity | `Paper.lean` | main agent |

Superseded or stopped: juno (independent GL attempt), charon (parallel equivariance),
iris (parallel Jacobi–Trudi). Agents that ended early (pallas, callisto, charon) were
resumed in the same session with the remaining step. Thread ids are recorded in
`/home/yang/kraw-lean-agents/<name>*.jsonl`; cards are in `/home/yang/kraw-lean-agents/cards/`.

## Fidelity audit (2026-10-03): Version 2.0.0 → 2.0.1

One Luna agent (`audit`, card `cards/audit.md`, report
`/home/yang/kraw-lean-agents/audit/AUDIT_REPORT.md`) compared every claim of the
Version 2.0.0 paper with its Lean statement under exact matching. It also rebuilt
the project, rechecked the axioms, and instantiated every indexed declaration at
concrete paper cells to rule out vacuous hypotheses. Findings and dispositions:

- `p_top_sub_one` (`p_{D-1} = (-1)^Q x`) carried an unused hypothesis
  `1 ≤ M + Q`, so it omitted the case `D = 0`. The hypothesis was removed.
- The Figure 1 caption read as assigning overlap cells to the flow region, while
  `Main.lean` tries the bulk case first. The caption now states a drawing
  convention ("drawn as flow").
- Four documentation errors were corrected in this file and in
  `certificates/CERTIFICATE_MAP.md`: the stale Phase 1 opening (two items), the
  `O₁`–`O₄` table labelled "§7", and orthogonality listed as a paper claim.

Every other claim matched exactly or by a stronger Lean statement.
