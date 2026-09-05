**Editorial referee report — 5 September 2026**

**Revision disposition — version 1.0.8, 5 September 2026**

Double-check: the source diff was compared with items 1.1–1.9 and the
copyedit table below; the corrected equation locators match the published
pages inspected in the review. The final saved LaTeX and BibTeX logs contain
no warnings, all 31 final PDF pages were inspected, and the source/PDF
reference inventory was checked after the final build.

The nine corrections are applied. Both Krasikov citations now point to
Theorem 5, (18), p. 79, with the Mařík–Dimitrov attribution in the detailed
discussion. The Bustoz–Ismail citation now points to Theorem 1, (2.3), p. 2.
The real-relaxation subject, Toeplitz-matrix description, discriminant
terminology, central transition, group identification, diagonal-matrix
description, printed-digest wording, and Figure 1 label have been corrected.

Gerhold–Kauers is added as methodological context. The Ayyer–Kumari and
Karmakar citations explicitly identify the arXiv versions whose theorem
numbers were inspected, and their bibliography entries link those versions.
The literature comparisons, region and subsection names, operational prose,
further questions, and local copyedits have been revised. The main title,
abstract, theorem, and verification programs retain their existing scope.

The QED placement and split checklist filename are corrected. Both tables
retain fixed placement after floating placement was found to interrupt the
proof or related-work discussion. In the final pagination, the two Szegő
entries are on the same page, so the repeated-author dash no longer begins a
page. No bibliography-style modification was necessary.

The final reference inventory contains 25 cited entries, 19 linked DOIs, and
65 unique source labels, with no unresolved literal references or missing
citation keys. All 18 linked verification-file paths exist at v1.0.6. The
verification programs, Makefile, and payload manifest are unchanged from
that version; the manuscript and repository metadata identify version 1.0.8.

Final PDF SHA-256:
`4fdd0ff59e64d624de053fcd64b272b32b458ce88c8be4f1e1d2fc11e6d948bd`.

This revision addresses the editorial review. Mathematical certificates were
not replayed. The original report below retains its version 1.0.7 page
numbers, metadata inventory, and review limitations; its source links are
pinned to the reviewed commit.

---

Manuscript: *Monotonicity of Turán determinants for binary Krawtchouk polynomials*, Leslie P. Polzer, version 1.0.7, dated 4 September 2026, 31 pages. Reviewed at commit `c0974a96ccc5fec3118f58e85757215006491091`.

**Recommendation: a focused minor editorial revision before arXiv posting.** The title identifies the subject clearly, the abstract states the normalization and the computational contribution, and the introduction gives readers a useful concrete example before the technical development. The paper does not call for a wholesale rewrite. The highest-priority changes are precise citation locators, a few ambiguous descriptions of mathematical objects, and one visible collision in Figure 1. The longer list of stylistic suggestions below is optional polishing.

This is a review of presentation, wording, bibliography, citation placement, and document production. I read the complete TeX source and bibliography, inspected all 31 rendered pages, performed an isolated document build, compared bibliographic metadata, and consulted the cited passages identified below. I did not assess proof correctness, replay the mathematical certificates, or establish originality. The initial review did not change the manuscript, bibliography, verification programs, or submission files.

Page numbers refer to the reviewed PDF. Source links point to the reviewed commit and retain its line numbers. The earlier [editorial report](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/notes/arxiv_editorial_review.md) reviewed version 1.0.6 and records its revision disposition; the present report concerns the remaining issues in version 1.0.7.

**1. Corrections to make before upload**

**1.1. Correct the Krasikov equation locator in both occurrences.** Pages 2 and 28; [introduction](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L271), [related work](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1894).

Double-check: I compared both manuscript citations with the displayed equation numbers on printed page 79 of the published article, including Theorem 5 and the attribution immediately preceding it. I also compared the credited author's name with reference [16] and the original article's metadata.

The fourth-degree refinement coupling two adjacent Turán determinants is **equation (18)**. Equation (17) is the preceding alternating-sum inequality. Both manuscript occurrences currently point to (17). Use **[Kra05, Theorem 5, (18), p. 79]**. The [published page](https://intlpress.com/site/pub/files/_fulltext/journals/maa/2005/0012/0001/MAA-2005-0012-0001-a005.pdf#page=5) makes the distinction explicit.

The attribution credits the second part to J. Mařík and its extension to the entire Laguerre–Pólya class to D. K. Dimitrov. Krasikov's prose misspells the surname; reference [16] and the [original article record](https://doi.org/10.21136/cpm.1964.117490) identify Jan Mařík. Preserve the attribution with that spelling. A suitable opening is:

> The inequality recorded in [Kra05, Theorem 5, (18), p. 79] couples two adjacent Turán determinants. Krasikov credits this refinement to Mařík and its extension to the full Laguerre–Pólya class to Dimitrov.

The introduction can use the shorter “the inequality recorded in” formulation. Retain Krasikov as the consulted source; there is no need to add unconsulted original references merely to expand the bibliography.

**1.2. Correct the Bustoz–Ismail equation locator.** Page 27; [source](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1868).

Double-check: I inspected the rendered published page 2 and compared the formula adjacent to each printed equation label with the manuscript's description of a weighted sum-of-squares representation.

The representation is **Theorem 1, equation (2.3)**. Equation (2.4) is an intermediate product identity in its proof. Replace “Section 2, especially (2.4)” with **“Section 2, Theorem 1, (2.3), p. 2.”** See the [published article in the EMIS mirror](https://emis.dsd.sztaki.hu/journals/HOA/IJMMS/Volume20_1/356195.pdf#page=2).

The source itself contains stale internal references to “Theorem 2.2” and “(2.4)” in prose below the theorem. Use the labels printed beside the theorem and representation, rather than copying those internal references. This correction concerns the locator; it does not assess the representation's applicability to the present proof.

**1.3. Name the quantity that can be negative in the real relaxation.** Page 2; [source](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L257).

The sentence “the corresponding real relaxation need not be nonnegative” has no explicit subject for “nonnegative.” Both Tur(s) and its difference Tₛ occur nearby, and the ensuing example concerns T₂. Replace the sentence with:

> The inequality Tₛ ≥ 0 can fail when the integer argument Q is replaced by a real q.

Then retain the displayed generating series and example. This removes an ambiguity without changing the example or the theorem.

**1.4. Identify the Toeplitz matrix explicitly.** Pages 3–4; [source](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L340).

After introducing a row of the binary Krawtchouk matrix, the text calls the displayed determinant “its adjacent 2 × 2 Toeplitz minor.” Grammatically, “its” points back to the Krawtchouk matrix. State that the Toeplitz matrix is formed from the coefficient row:

> For a fixed integer argument Q, the values (pₛ) form a row of the binary Krawtchouk matrix. The Toeplitz matrix formed from this coefficient row has adjacent 2 × 2 minors of the form

followed by the existing determinant display. The next sentence can begin directly with “Corollary 1.3 identifies these minors…”. This also removes the awkward page break between the determinant on page 3 and “is its…” on page 4.

**1.5. Use one discriminant convention.** Pages 6 and 17; [first occurrence](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L485), [remark](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L515), [later occurrence](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1206).

Double-check: I compared the expressions called “discriminant” at these locations. The first is written as 4AC − B², whereas the later usage follows the B² − 4AC convention.

Call the first expression the **negative discriminant** and use that noun consistently in the following remark. The formulas need not change. Also replace the ambiguous pronoun in “re-expressing Tₛ in a shifted basis multiplies it by a positive square” with the intended noun, so readers do not momentarily read “it” as Tₛ. For example:

> The sign of the negative discriminant is unchanged under the indicated basis changes: expressing Tₛ in a shifted recurrence basis multiplies the negative discriminant by a positive square.

This is a terminology recommendation, not a check of the basis-change formula.

**1.6. Remove the undefined central index from the transition sentence.** Page 7; [source](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L554).

Double-check: I searched the source for definitions of c and read the surrounding passages. The transition uses p_c and p_{c+1}; the explicit definitions c = D/2 and c = (D − 1)/2 occur later in Section 5, at lines 1230 and 1234.

The transition also presents one central relation as the initial condition for both later recurrence arguments, although their initial-value discussions distinguish parity cases. A simpler signpost avoids introducing an index and prematurely summarizing the cases:

> The recurrence arguments in Sections 5 and 6 start from reflection constraints at the center.

Alternatively, define c at this point and qualify the displayed relation by its stated parity conditions. The short signpost is preferable editorially.

**1.7. Make the character terminology precise at first use.** Pages 3 and 28; [Proposition 1.4](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L294), [related work](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1908).

In Proposition 1.4, write “the irreducible polynomial-character value of GL_D(ℂ)” so the group is named at the first formal identification.

Double-check: the theorem's parameter range includes Q = 0; substituting that value into the displayed diagonal matrix gives I_D. Thus “the order-two element” is too specific for the full stated range.

In Section 8, replace that phrase with **“the diagonal matrix diag(I_M, −I_Q)”**. This avoids an exact-order assertion while retaining the intended specialization. No change to the allowed parameter range is called for.

**1.8. Correct the description of what is printed with the submission.** Page 26; [source](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1756).

“This digest identifies the proof payload printed with this submission” suggests that the files themselves are printed in the article. The preceding display prints the digest, while Section 7.3 identifies the accompanying files in the repository. Use:

> This printed digest identifies the accompanying verification files; the full manifest additionally binds the article and the PDF built in the reference toolchain.

**1.9. Move the Figure 1 flow label away from the right border.** Page 10; [TikZ nodes](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L757).

Double-check: I inspected page 10 at full-page resolution and compared the label placement with the two TikZ nodes centered at x = 5.35 and the frame at x = 6.

The right-hand end of “(Thm 3.3)” collides with the vertical border. Move both flow-label nodes left, keeping them aligned; then inspect the rendered result. There is no need to shrink the text. The figure's schematic qualification and grayscale distinction are useful and should remain.

**2. Literature positioning and bibliography recommendations**

**2.1. Describe what earlier papers state without asserting a stronger nonimplication.** Page 28; [source](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1915).

The sentence ending “nor do they imply their positivity in the present specialization” makes a stronger logical claim than a literature summary requires. It can sound as though all consequences of the cited character formulas have been excluded. Prefer:

> These works give formulas for individual character values. Here we study their positivity and ordering as the rectangle height varies.

Keep the concrete distinctions of specialization, varying shape, and normalization. Those are more informative than repeatedly saying that no implication is asserted. The related caveats in Section 1.4 and the two normalization comparisons in Section 8 could be shortened once the distinction has been stated clearly.

The final “To our knowledge” novelty sentence is appropriately qualified. This editorial review does not certify that novelty claim.

**2.2. Add one methodological reference on computer proofs of Turán inequalities.** Suggested addition to Section 8, or a short sentence in Section 7.1.

Double-check: searches of the manuscript and bibliography for Gerhold, Kauers, and cylindrical algebraic decomposition returned no occurrences. I then read Section 2 of Gerhold–Kauers's published paper and checked its bibliographic header and the author's publication list.

Stefan Gerhold and Manuel Kauers, *A computer proof of Turán's inequality*, **J. Inequal. Pure Appl. Math. 7(2) (2006), Article 42**, is a directly relevant methodological antecedent. Its Section 2 explains the use of induction, Tarski formulas, and cylindrical algebraic decomposition for a Turán inequality. See the [published paper](https://fam.tuwien.ac.at/~sgerhold/pub_files/papers/2006_turan.pdf) and [author's bibliography](https://fam.tuwien.ac.at/~sgerhold/publications.html).

A concise addition would be:

> Gerhold and Kauers [GK06, Section 2] describe a computer algebra proof of a Turán inequality using induction and cylindrical algebraic decomposition.

This supplies methodological context; it does not claim that their procedure supplies the present theorem. Adding this reference is a recommendation, rather than a correction to an existing entry. If it becomes an additional strand in Section 8, update “Five strands” accordingly, or use the unnumbered phrase “The following directions are closest to the present theorem.”

Suggested BibTeX, using the manuscript's existing URL-rendering convention:

```bibtex
@article{gerholdkauers06,
  author  = {Gerhold, Stefan and Kauers, Manuel},
  title   = {A computer proof of {T}ur{\'a}n's inequality},
  journal = {J. Inequal. Pure Appl. Math.},
  volume  = {7},
  number  = {2},
  year    = {2006},
  pages   = {Article~42},
  note    = {\url{https://fam.tuwien.ac.at/~sgerhold/pub_files/papers/2006_turan.pdf}},
}
```

**2.3. Distinguish checks against published versions from checks against preprints.**

Double-check: the source comparisons below used the specific editions or versions listed, rather than inferring theorem numbers from metadata.

| Citation in the manuscript | Passage inspected | Editorial disposition |
|---|---|---|
| [Mac95], Chapter I, (3.5), p. 41 | Second edition, printed p. 41 | The dual Jacobi–Trudi locator is correctly placed. |
| [Mac95], Chapter I, Appendix A, (8.2), (8.4), pp. 162–163 | Second edition, those printed pages | The character-identification locator is correctly placed. |
| [Kra05], Theorem 5, (17) | Published article, printed p. 79 | Change (17) to (18) in both manuscript locations; see item 1.1. |
| [BI97], Section 2, (2.4) | Published article, printed p. 2 | Point to Theorem 1, (2.3); see item 1.2. |
| [AK22], Theorem 2.5 | arXiv:2109.11310v3, p. 6, including the preceding attribution | The present Littlewood–Prasad attribution matches that passage. Published-version numbering was not independently checked. |
| [Kar25], Theorem 4.1 | arXiv:2412.17324v1, Section 4 | The cited location in that version discusses the general linear setting. Published full text was inaccessible during this review, so journal-version numbering remains unchecked. |
| [KLS10], Section 9.11 | Publisher's table of contents and foreword | Section 9.11 is “Krawtchouk,” beginning on p. 237. The section's individual normalization formulas were outside this editorial check. |

The Macdonald passages are available in the [second-edition scan](https://math.berkeley.edu/~corteel/MATH249/macdonald.pdf#page=52). The preprint passages are in [Ayyer–Kumari v3](https://arxiv.org/pdf/2109.11310v3#page=6) and [Karmakar v1, Section 4](https://arxiv.org/html/2412.17324v1#S4). The Krawtchouk section locator is listed in the [publisher's book front matter](https://link.springer.com/content/pdf/bfm:978-3-642-05014-5/1).

For [AK22] and [Kar25], adding the accessible arXiv identifiers alongside the journal references would help readers. Before relying on a journal-version theorem number, compare it with that version; otherwise make the preprint version used for the locator explicit. This is an access/version limitation of this review, not a finding that either locator is wrong.

**2.4. Entry-by-entry metadata audit.**

Double-check: I compared the 19 DOI-bearing entries with their Crossref records and consulted publisher, author, original-title-page, arXiv, or official software records for the additional details noted below. I also compared the rendered references with the `.bib` file. These checks revealed no substantive author, title, publication-year, volume, issue, page-range, or identifier correction to the existing 24 entries. The two equation-locator corrections concern citations in the body.

The table records metadata checks only; it does not imply that every statement attributed to every source has been checked mathematically.

| Rendered key | Metadata checked | Result or specific note |
|---|---|---|
| [AK22] | Ayyer–Kumari; J. Algebra 609 (2022), 437–483; [DOI](https://doi.org/10.1016/j.jalgebra.2022.06.015) | Retain. The preprint-version qualification above applies to the theorem locator. |
| [BI97] | Bustoz–Ismail; Int. J. Math. Math. Sci. 20(1) (1997), 1–7; [DOI](https://doi.org/10.1155/S016117129700001X) | Retain 1–7. The scanned article ends on printed p. 7; its opening masthead says 1–8, but the registry and institutional record use 1–7. |
| [BS09] | Berg–Szwarc; J. Approx. Theory 161(1) (2009), 127–141; [DOI](https://doi.org/10.1016/j.jat.2008.08.010) | Retain 2009; the year embedded in the DOI is not the publication year. |
| [CC89] | Craven–Csordas; Pacific J. Math. 136(2) (1989), 241–260; [DOI](https://doi.org/10.2140/pjm.1989.136.241) | Retain. |
| [Del73] | Delsarte; Philips Research Reports Supplements, no. 10 (1973); publisher and Eindhoven | Retain; checked against the [original monograph](https://users.wpi.edu/~martin/RESEARCH/philips.pdf). |
| [Kah26] | Stefan Kahler; title, 2026, arXiv:2605.05180v1 | Retain the spelling “Kahler” and the versioned [arXiv reference](https://arxiv.org/abs/2605.05180v1). |
| [Kar25] | Karmakar; Proc. Indian Acad. Sci. Math. Sci. 135(2) (2025), Article 41; [DOI](https://doi.org/10.1007/s12044-025-00847-0) | Retain the journal year and explicit article number. |
| [KL96] | Krasikov–Litsyn; J. Combin. Theory Ser. A 74(1) (1996), 71–99; [DOI](https://doi.org/10.1006/jcta.1996.0038) | Retain. |
| [KLS10] | Koekoek–Lesky–Swarttouw; book title, series, Springer, 2010; [DOI](https://doi.org/10.1007/978-3-642-05014-5) | Retain; preserve the accent in René. |
| [Kra01] | Krasikov chapter; *Codes and Association Schemes*, DIMACS 56 (2001), 193–198; editors Barg and Litsyn; [DOI](https://doi.org/10.1090/dimacs/056/15) | Retain. Chapter and parent-volume metadata identify the same collection. |
| [Kra03] | Krasikov; Anal. Appl. 1(2) (2003), 189–197; [DOI](https://doi.org/10.1142/S0219530503000120) | Retain 189–197. |
| [Kra05] | Krasikov; Methods Appl. Anal. 12(1) (2005), 75–88; [DOI](https://doi.org/10.4310/MAA.2005.v12.n1.a5) | Entry metadata is correct; repair the body locators and attribution. |
| [Kra11] | Krasikov; J. Approx. Theory 163(9) (2011), 1269–1299; [DOI](https://doi.org/10.1016/j.jat.2011.04.004) | Retain. |
| [Lev95] | Levenshtein; IEEE Trans. Inform. Theory 41(5) (1995), 1303–1321; [DOI](https://doi.org/10.1109/18.412678) | Retain. |
| [LW00] | Li–Wong; J. Approx. Theory 106(1) (2000), 155–184; [DOI](https://doi.org/10.1006/jath.2000.3474) | Retain. |
| [Mac95] | Macdonald; second edition, Oxford Mathematical Monographs, Clarendon Press, 1995; [DOI](https://doi.org/10.1093/oso/9780198534891.001.0001) | Retain; do not replace the edition date with a later electronic-publication date. |
| [MS77] | MacWilliams–Sloane; North-Holland Mathematical Library 16, 1977 | Retain; checked against the [publisher preview](https://api.pageplace.de/preview/DT0400.9780080954233_A23544044/preview-9780080954233_A23544044.pdf). |
| [MSP+17] | Meurer et al.; PeerJ Comput. Sci. 3 (2017), e103; [DOI](https://doi.org/10.7717/peerj-cs.103) | Retain; the full author list agrees with [SymPy's official citation](https://docs.sympy.org/latest/citing.html), including “AMiT Kumar.” |
| [Pol26] | Polzer; verification artifact, version 1.0.6, 2026 | Retain the [specific release](https://github.com/skypher/kraw/releases/tag/v1.0.6); see item 5 below. |
| [RS98] | Reiner–Stanton; J. Algebraic Combin. 7(1) (1998), 91–107; [DOI](https://doi.org/10.1023/A:1008623312887) | Retain. |
| [Sze48] | Szegő; Bull. Amer. Math. Soc. 54(4) (1948), 401–405; [DOI](https://doi.org/10.1090/S0002-9904-1948-09017-6) | Retain; keep the correctly accented author name. |
| [Sze75] | Szegő; fourth edition, AMS Colloquium Publications 23, 1975 | Retain; edition and series are also recorded in the [NIST bibliography](https://dlmf.nist.gov/bib/S). |
| [Szw98] | Szwarc chapter; *Harmonic Analysis and Hypergroups*, 165–182, 1998; six editors; [publisher record](https://link.springer.com/chapter/10.1007/978-0-8176-4348-5_11) | Retain 1998. The 2007 arXiv deposit is not the chapter's publication date. |
| [Szw21] | Szwarc; J. Approx. Theory 270 (2021), Article 105618; [DOI](https://doi.org/10.1016/j.jat.2021.105618) | Retain 2021. The internal key `szwarc20` is invisible to readers and does not require renaming. |

The present bibliography consistently identifies article numbers and provides usable DOI links. The full SymPy author list is long but appropriate to the selected style; shortening it is a stylistic choice, not a bibliographic correction. Do not change the stated SymPy 1.12 dependency to the current software version: that sentence records the version used by the project.

**3. Organization, reader guidance, and line editing**

**Keep the present title, abstract, example, and normalization subsection.** The abstract is now self-contained about the coefficient convention, defines Tur(s), and distinguishes the three types of argument. The numerical example on page 2 gives readers a quick view of the asserted phenomenon. Section 1.4 explains why the normalization is part of the statement. These features work well.

**The introduction now contains enough literature orientation for an imminent submission.** A full related-work section on pages 27–28 is acceptable because the introduction already names the closest Krawtchouk references. As an optional improvement, place one concise contribution sentence near the introductory comparison, drawing on the final paragraph of Section 8. Moving the entire related-work section is unnecessary.

**Standardize the names of the proof regions.** The section headings say “Gap cells with even Q” and “Gap cells with odd Q,” but theorem titles and prose still use “even-minimum” and “odd-minimum.” Use “even Q” and “odd Q” in mathematical exposition, after the existing convention Q ≤ M. Likewise, use “fixed-argument” consistently in place of alternating “per-Q,” “fixed-Q,” and “fixed-argument.” Keep the exact names of versioned programs and log files when identifying those files.

At lines 1617 and 1634, prefer “computer-assisted” to “machine-dependent” and “machine-assisted.” The distinct phrase “resource values are machine-dependent” at line 1786 is appropriate and should remain.

**Tighten the operational prose in Section 7 without removing the certificate specifications.** The distinction between file identity, program execution, and independent implementation is useful. State each once prominently. The catalogue of make targets at lines 1772–1786 and the description of an external signoff form can be shortened by linking to the README. Preserve Section 7.2's concrete specifications, the program-to-log mapping, and Table 2; those tell readers what accompanies the paper.

**Split dense multi-claim paragraphs in Section 4.2.** The sector-sign argument and the subsequent nondegeneracy discussion ask readers to track several objects, tests, and thresholds in a single paragraph. Shorter sentences separating construction, sign test, and exceptional-case handling would help. Retain the displayed bounds and the worked u = 4 certificate. This is a request for sentence-level navigation, not a different proof organization.

**Clarify the language of the further questions.** Page 29; [source](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1947).

Double-check: “paired cone” occurs once in the source, in the first further question, without a definition under that name.

Refer explicitly to the coefficient-pairing conditions in Theorem 4.5, or define the proposed cone before asking whether it is preserved. In the second question, specify which parameter ranges and normalization are being contemplated. “For which choices of a and b, and which normalization, does an analogous monotonicity statement hold?” is clearer than an unrestricted persistence question. “Roots interlace across 0” also needs a precise intended meaning. These are requests to make the questions intelligible, not proposed answers to them.

**Suggested local copyedits.** Except for the punctuation repair, these are preferences rather than defects. Formulae are represented in Unicode here for readability; keep the manuscript's normal TeX notation when applying them.

| Source location | Current wording | Suggested wording or action |
|---|---|---|
| [243](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L243) | “A small row illustrates the statement. For…” | “For example, take (M,Q) = (5,2).” |
| [253](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L253), [1861](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1861) | “fixed degree window” | “fixed degree index n”; use the same description in both literature discussions. |
| [423](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L423) | “step-1 recurrence (contiguous in s; from the log-derivative…)” | “Logarithmic differentiation of the generating function gives the recurrence…” |
| [538](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L538), [1471](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1471) | “iff” | “if and only if” in running prose. |
| [804](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L804) | “trivial (T_D = 1)” | “endpoint identity T_D = 1”. |
| [837](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L837) | “feeding this single constraint through…” | “combining this reflection constraint with…”; complete the sentence with the existing recurrence description. |
| [902](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L902) | “a cell is proved” | “Tₛ ≥ 0 follows at that cell.” |
| [943](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L943) | “the alternate pinning … takes over” | “we use the alternative reflection constraint…”. |
| [962](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L962) | “To make the computational mechanism inspectable…” | “We illustrate the certificate construction with u = 4 and ε = +1.” |
| [1101](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1101), [1522](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1522) | “Q = min(M,Q)” | “Q ≤ M”, consistent with the relabeling convention. |
| [1173](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1173) | “Define (j runs over top-half indices)” | “For each top-half index j, define”. |
| [1187](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1187) | Display ends with a comma, followed by “We call…” | End the display with a period. |
| [1229](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1229) | “Anchors from the reflection” | “Reflection supplies the initial values.” |
| [1337](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1337) | “For transparency, its symbolic obligations are specified here.” | “Its symbolic obligations are as follows.” |
| [1494](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1494) | y₊(“first window”) inside a formula | Write the actual arguments y₊(2) and y₊(1) in the respective parity cases already described in the next sentence. |
| [1670](https://github.com/skypher/kraw/blob/c0974a96ccc5fec3118f58e85757215006491091/paper/krawtchouk_turan_positivity.tex#L1670) | “The inputs are not opaque expanded expressions…” | State directly that the inputs are defined recursively by the specified chain. |

The AI-use disclosure is clearly separated from the mathematical text and explicitly assigns responsibility to the author. Its wording does not require an editorial change.

**4. Layout and typography**

Double-check: I inspected contact sheets covering all 31 pages and opened the figure, inventory, and final bibliography page at larger size. I also compared page boundaries with the extracted PDF text.

The document is generally legible. The theorem hierarchy, equation numbering, running heads, and table styles are consistent. Table 2's log names fit, its two columns remain distinct, and the caption accurately describes an inventory. Apart from the Figure 1 collision in item 1.9, the following are optional refinements:

- **Page 7:** the proof of Theorem 3.2 leaves its QED square on a line of its own after the final display. Put `\qedhere` in that display if the same placement remains after editing.
- **Pages 3–4:** the determinant is separated from its grammatical continuation. Item 1.4 supplies a wording fix that also improves the page break.
- **Pages 23–24:** `certificates/REVIEW_CHECKLIST.md` is split across the page boundary. Use a short descriptive link such as “referee checklist” in the running sentence; retain exact paths in the inventory or repository documentation.
- **Pages 10 and 26:** fixed-position tables contribute to the substantial blank space below the preceding text. Ordinary table placement such as `[tbp]` may improve page balance. Keep Figure 1 after the preceding proof so that it does not interrupt the argument again.
- **Page 31:** [Sze75] starts the page with a repeated-author dash, while the author's name appears only on page 30. If this boundary persists, prefer repeating “Gábor Szegő” at the new page. Implement that through the bibliography formatting rather than treating a hand edit to generated `.bbl` as permanent.

Keep the present readable table font sizes. A shorter page count is not itself a goal, and the final page containing three references is unobjectionable.

**5. Document production and arXiv packaging**

Double-check: I reread the saved final LaTeX/BibTeX logs, compared SHA-256 digests of the original and rebuilt PDF and bibliography, inspected font and PDF metadata, and checked the saved label, citation, DOI-target, and versioned-path audit results.

| Check actually performed | Result |
|---|---|
| Full `make paper` workflow in a temporary copy | Completed successfully. |
| Saved final LaTeX and BibTeX logs | No warnings, undefined references/citations, or overfull/underfull boxes reported. |
| Rebuilt versus supplied PDF | Byte-identical; 31 pages, PDF 1.5, 616,300 bytes. |
| Rebuilt versus supplied `.bbl` | Byte-identical. |
| Source labels and literal references | 65 unique labels; no unresolved literal references. |
| Bibliography/citation inventory | 24 entries, all cited; no missing citation keys. |
| DOI rendering | All 19 DOI URLs occur as PDF link targets; visible DOI-note URLs agree with the `.bib` DOI fields. |
| Fonts | Embedded and subsetted; no Type 3 fonts. |
| PDF metadata and navigation | Title and author present; References and AI-use disclosure have bookmarks. |
| Versioned repository file links | All 18 linked file paths exist at tag v1.0.6. |
| Public verification release | GitHub's release API identifies v1.0.6 as public and non-draft. |
| Version relationship | No diff from v1.0.6 in `scripts/`, `cpp/`, or `certificates/PAYLOAD.sha256`. |
| Printed payload-manifest digest | Matches the current `PAYLOAD.sha256` file. |

The reviewed PDF's SHA-256 digest is `421969a1936f4f5dcc77061e8cb3fa1a9afb78932455924a31d8686f615dcb2e`. These are document-production and artifact-identity checks. They are not a replay or validation of the mathematical computations.

The manuscript's version 1.0.7 and the verification artifact's version 1.0.6 are explicitly distinguished in Section 7.3. That distinction is appropriate for unchanged verification files. Do not mechanically change all artifact references to v1.0.7 during an editorial revision.

For the source upload, follow the current [arXiv TeX instructions](https://info.arxiv.org/help/submit_tex.html): arXiv supports `.bib` files; a supplied `.bbl` is optional and takes precedence. If supplying the `.bbl`, regenerate it from the final bibliography and keep its basename aligned with the main `.tex` file. A stale `.bbl` could otherwise conceal the added or corrected references.

The main TeX source, bibliography, and matching generated `.bbl` can be packaged together. The figure is inline TikZ, so it does not require a separate image asset. Omit local build products such as `.aux`, `.log`, and `.blg`, this review report, and unrelated repository files from the source submission. Do not include the compiled PDF alongside the TeX source merely as another source file. After the editorial changes, update any repository manifest that binds the changed manuscript and generated PDF, then inspect arXiv's generated PDF before final submission. The local build does not substitute for that final preview.

The initial review did not perform an arXiv submission, release publication, commit, or manuscript edit.
