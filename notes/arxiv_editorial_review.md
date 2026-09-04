**Editorial referee report — 4 September 2026**

**Revision disposition — manuscript version 1.0.7.** The citation, abstract,
wording, terminology, inventory, and layout corrections below have been
applied. The introduction now presents the example and closest literature
comparison earlier; repeated introductory and software-dependency prose has
been condensed. The bibliography adds SymPy and the verification artifact,
renders DOI/arXiv links, and identifies article numbers explicitly. References
and the AI-use disclosure have PDF bookmarks. The manuscript and repository
metadata identify version 1.0.7, while the unchanged verification code and logs
are cited through the existing v1.0.6 release.

Double-check: the final saved LaTeX and BibTeX logs contain no warnings;
all 31 rendered pages were inspected. The generated bibliography has 24
entries, all cited, and all 19 DOI links occur as PDF link targets. All 65
source labels are unique, all literal references resolve, and the 18 linked
artifact paths exist at v1.0.6. `make payload-check` passes; the verifier
sources and payload manifest have no diff from v1.0.6. These checks concern
document production and artifact identity, not a new mathematical review.

The original report below records the review of version 1.0.6. Its page
numbers, publication audit, and source links refer to that version.

Manuscript: *Monotonicity of Turán determinants for binary Krawtchouk polynomials*, Leslie P. Polzer, version 1.0.6, 30 pages. Reviewed against commit `7955273411dd42d6102d0e8858da869b6fa8f204`.

**Recommendation: make a focused editorial revision before posting.** The manuscript has a clear principal statement, useful normalization guidance, and unusually explicit descriptions of its computational components. Its presentation is close to submission-ready. The changes with the greatest immediate value are two citation corrections, a self-contained abstract, clearer verification-file identification, and removal of several awkward or overstated sentences. Broader restructuring would improve the reading experience but is optional for this submission.

This report covers presentation, wording, bibliography, citation placement, and document production. I read the complete TeX source and bibliography, inspected all 30 rendered pages, rebuilt the document in a temporary directory, and consulted external bibliographic records and selected cited passages. I did not assess the correctness of the proof, replay the mathematical certificates, or establish originality. The initial review did not modify the manuscript or bibliography.

Page numbers below refer to the reviewed PDF; source links point to the reviewed commit and retain its line numbers. “Correction” identifies a concrete documentary or wording problem; “recommendation” identifies an editorial judgment.

**1. Corrections and high-priority improvements before upload**

**1.1. Correct the Macdonald locator and attach each citation to its actual use.** Page 3, [source line 280](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L280).

Double-check: I compared the manuscript's citation with Macdonald's Chapter I, formula (3.5), and Appendix A, formulas (8.2) and (8.4), including the printed pages containing the character statement.

Chapter I, §3 is the appropriate location for the Schur-function determinant identities. The character identification used in the next sentence should point to Chapter I, Appendix A, §8. The present reference to “Chapter I, Section 3” after the character sentence sends the reader to the wrong location for that assertion. Use:

- After “the dual Jacobi–Trudi identity”: **[Mac95, Chapter I, (3.5), p. 41]**.
- After the sentence identifying irreducible polynomial characters: **[Mac95, Chapter I, Appendix A, (8.2) and (8.4), pp. 162–163]**.

These locators distinguish the determinant formula from its representation-theoretic interpretation. See the [book scan, printed p. 41](https://math.berkeley.edu/~corteel/MATH249/macdonald.pdf#page=52), [printed p. 162](https://math.berkeley.edu/~corteel/MATH249/macdonald.pdf#page=173), and [printed p. 163](https://math.berkeley.edu/~corteel/MATH249/macdonald.pdf#page=174).

**1.2. Preserve the original attribution in the Ayyer–Kumari citation.** Page 27, [source line 1901](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1901).

Double-check: the introduction and the paragraph immediately preceding Theorem 2.5 in Ayyer–Kumari's version 3 both identify the general-linear-group result as due to Littlewood and independently Prasad. The theorem itself cites their sources.

“Ayyer and Kumari [AK22, Theorem 2.5] factor characters…” obscures this attribution. A replacement that retains the source actually used is:

> The factorization theorem of Littlewood and Prasad, presented in [AK22, Theorem 2.5], treats general linear characters under balanced root-of-unity specializations.

The relevant passage is on [page 6 of Ayyer–Kumari's version 3](https://arxiv.org/pdf/2109.11310v3#page=6). Adding the original references is optional if this “presented in” wording is used; any new direct citation should identify the edition and locator actually consulted.

**1.3. Make the abstract self-contained.** Page 1, [source line 149](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L149).

The body explicitly extends the coefficient sequence by zero, but the abstract omits that convention even though its displayed inequality uses indices beyond the degree. Add it. The abstract also introduces the symbol `Tur(s)` without defining that abbreviation; either define it before the inequality or write “the determinants are at least 1.”

Replace the second “Equivalently” with “By the dual Jacobi–Trudi identity”: this introduces an interpretation more clearly. Include the body's qualification D ≥ 1 when referring to GL_D. Replace “accompanying repository artifact” with “accompanying repository.” A complete proposed abstract appears below.

**1.4. Make Table 2 identify the files it promises to identify.** Page 26, [source line 1788](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1788).

Double-check: I compared the table with the filenames in `cpp/`, `certificates/`, and the certificate map.

The introduction says every row names a program and its output. Several entries are output stems, however, and the program names differ:

| Current table entry | Actual program | Output |
|---|---|---|
| `exhaustive-scan-D1200` | `cpp/exhaustive-turan-scan.cpp` | `certificates/exhaustive-scan-D1200.txt` |
| `independent-scan-D1200` | `cpp/independent-pascal-scan.cpp` | `certificates/independent-scan-D1200.txt` |

The smallest correction is to label the first column **“Verification task / log stem”**, revise the introductory sentence accordingly, and link the exact program-to-output mapping in `CERTIFICATE_MAP.md`. A more substantial alternative is to give distinct program and output columns. The mutation-test summary also describes a group of tasks, so the former solution fits the table particularly well. Do not make readers infer filenames from these stems.

**1.5. Link the release actually associated with the paper.** Pages 25–26, [source line 1736](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1736).

Double-check: the GitHub release record identifies a public, non-draft v1.0.6 release, published on 4 September 2026. Its exact URL is available now.

Replace the generic releases-page link with the [v1.0.6 release](https://github.com/skypher/kraw/releases/tag/v1.0.6). The paragraph should foreground present availability; the promise of a future journal archive is secondary. “Distribution mirror” is also confusing when no original archival location has been identified. “Distribution site” is sufficient.

Suggested opening, for the currently reviewed version:

> The source, verification programs, deterministic logs, and manuscript PDF for version 1.0.6 are available in the versioned release [link]. The manifest identifies the files in that release.

Retain the distinction between file integrity and execution evidence. A formal bibliography entry for the versioned software release would make this material easier to cite. After applying edits, update the manuscript version, release reference, and manifests together so the availability statement describes the submitted files.

**1.6. Make the DOI information visible.** References, pages 29–30; [bibliography-style selection](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1981).

Double-check: the bibliography contains 18 DOI fields; none of those DOI strings occurs in the generated `.bbl`. I also inspected the rendered references.

The existing `amsalpha` output discards all 18 DOI fields. The records are identifiable from their conventional metadata, so this is an accessibility improvement rather than an arXiv acceptance requirement. Nevertheless, rendering linked DOIs would materially improve the reference list. Use one consistent method that preserves the desired bibliography style, and check the generated bibliography rather than relying on the `.bib` fields alone. Make the existing arXiv identifiers clickable as well.

**1.7. Correct definite prose and terminology errors.** The line-edit table below contains the full list. The most immediate corrections are both occurrences of “linear decreasing,” “positivity is inspection,” and the description of Krawtchouk coefficients as “every binomial coefficient.” These are small edits with a clear improvement in accuracy and fluency.

**2. Organization, reader guidance, and tone**

**Bring the closest literature comparison into the introduction.** The principal theorem appears on page 2, but the detailed comparison with Krasikov appears only on page 27. Readers deciding what the contribution is should not have to reach the end of the technical argument. Insert a short paragraph after the theorem and corollaries naming the closely related Krawtchouk results and explaining the degree-index comparison and normalization being studied. Preserve the exact scope of the existing comparisons; moving them earlier is not a new originality claim.

Keep the longer related-work section if desired. For an imminent submission, adding a concise introductory paragraph is less disruptive than relocating the whole section.

**Condense §1.3.** Pages 3–4, [source line 313](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L313). This subsection repeats the positive-integer conclusion, the endpoint value, the ordering of the lattice indices, and the significance of the chosen normalization. Those points already appear in the corollaries and adjacent discussion. Retain the Toeplitz-minor interpretation and the concrete (M,Q) = (5,2) example; shorten the surrounding explanation. “Adjacent minors and lattice indices” would be a more informative heading than “Why this minor sequence is natural.”

The example is one of the best aids to comprehension. Placing it immediately after the corollaries would show the reader the phenomenon before the more specialized Schur discussion. The normalization subsection should remain: it explains an essential feature of the statement to readers familiar with other Krawtchouk conventions.

**Introduce the recurring proof vocabulary at first use.** “Cell,” “pinning,” and “gap window” carry substantial organizational meaning but initially read as project-specific shorthand.

- Define a **cell** as an admissible parameter/index triple when the finite scan is introduced; explain its later expression in (D,x,u) coordinates.
- Explain **pinning** as the selected reflection constraint when introducing the two constraints in §4.2.
- Motivate and define the **gap window** before the opening construction in §6.1. The phrase occurs at line 1303, while its role is explained later in the argument.
- Consider headings **“Gap cells with even Q”** and **“Gap cells with odd Q”** in place of “even-minimum” and “odd-minimum,” after reminding the reader that Q is the smaller exponent.

These changes would make the transitions between sections easier to follow without changing any displayed mathematics.

**Reduce repeated discussion of computer assistance.** The three-way distinction in §1.6 is useful: written arguments, symbolic certificates for finite families, and a finite exhaustive scan. Keep that early explanation. Sections 7.1 and 7.3 then repeatedly explain exact arithmetic, independent implementations, hash integrity, and the absence of external human replay attestation.

State each distinction once, in a clear paragraph, and use cross-references elsewhere. Keep §7.2's certificate specifications and the theorem-to-program inventory, which give substantive information. In particular, preserve the difference between an independent implementation and an independent human replication; shortening should not blur it.

Possible headings:

| Current heading | Suggested heading |
|---|---|
| Proof status and computer assistance | Computer-assisted components |
| Machine verification | Computer-assisted verification |
| Availability and trust boundary | Code availability and software dependencies |

“Proof status” sounds like an internal progress record. A submitted article benefits from headings describing the argument itself.

**Narrow broad literature comparisons to the cited results.** Pages 27–28, [source line 1894](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1894).

| Current wording | Suggested treatment |
|---|---|
| “the closest explicit antecedent” | “a closely related antecedent,” unless the superlative is essential and supported by a sufficiently comprehensive comparison |
| “so neither result implies the other” | Describe the different specializations and sequences of shapes directly; this is clearer than asserting mutual nonimplication in a literature survey. |
| “Neither line of work treats…” | Restrict the sentence to the cited results: “The cited results address coefficient inequalities and asymptotic expansions; the present theorem concerns degree-index monotonicity at a fixed integer argument.” |
| “We are not aware…” followed by “We did not find…” and “Our novelty claim is limited…” | Consolidate into one appropriately qualified sentence about the exact theorem and normalization. |

A possible final sentence is: “To our knowledge, Theorem 1.1 has not previously been stated for this coefficient normalization.” This is proposed author wording; the present review is not an exhaustive novelty search.

The opening historical phrase “answering a question of P. Turán” can also be simplified. “The classical Turán inequality for Legendre polynomials, discussed by Szegő [Sze48], …” avoids making an unnecessary claim about who posed or first solved what. Kahler's historical footnote credits Turán with the result and describes its communication to Szegő; I could not retrieve the original 1948 PDF directly in this review, so this is a recommended neutral wording rather than a conclusion from inspection of that original article. See [Kahler, footnote 2](https://arxiv.org/html/2605.05180v1).

**3. Layout and typography**

**Reposition Figure 1 to avoid interrupting Lemma 3.6.** Pages 9–10, [source line 725](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L725). In the rendered PDF, page 9 ends inside the proof at the displayed formula for U₋. Figure 1 occupies the top of page 10, and the sentence beginning “putting t…” resumes below it. This separates an equation from the sentence that immediately uses it. Place the figure at the following subsection boundary or constrain its float placement so that the short proof reads continuously.

**Clarify what the shading assigns.** The caption says the bulk and flow regions are separated by the circle. The preceding coverage argument discusses a bulk margin at the flow boundary, so the graphic is best described as an assignment of coverage regions. Add a sentence such as: “For this schematic, the overlap of the bulk and flow regions is assigned to the flow region.” This avoids asking the figure to represent the full domains of both arguments as disjoint. Keep the current indication that the picture is schematic and that the admissible lattice has parity constraints.

**Balance the title lines.** Page 1. The current second line consists solely of “polynomials.” A deliberate break after “determinants” would produce two informative lines without changing the title. There is also substantial manually imposed space around the title and abstract, including the skip at [line 174](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L174). Modestly reducing that space may improve the opening page, but fitting the theorem on page 1 is not itself a requirement.

**Improve Table 2's scanability without shrinking its font.** The table on page 26 is dense. Shorter task descriptions and a little more row spacing would help. If exact filenames are added, wrap them deliberately and give the descriptive column sufficient width. The enlarged rendering is readable; this is a refinement, not a clipping defect.

**Add a References bookmark.** The PDF has section and subsection bookmarks, but the starred References and AI-use disclosure sections do not appear in the outline. References is particularly useful as a navigation destination. The running heads, theorem styling, equation numbering, and grayscale figure are otherwise visually consistent. The partial final bibliography page is normal and does not justify compressing the document simply to remove a page.

**4. Specific wording edits**

These supplement the larger issues above. Where a replacement depends on the surrounding sentence, the intended edit is described rather than supplied as an isolated fragment.

| Source location | Current wording or issue | Suggested revision |
|---|---|---|
| [149](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L149) | Abstract omits the zero-extension convention. | Add “with pₛ = 0 outside 0 ≤ s ≤ D.” |
| [158](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L158) | `Tur(s)` is not defined in the abstract. | Define it before the inequality, or use “the determinants are at least 1.” |
| [165](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L165) | “accompanying repository artifact” | “accompanying repository” |
| [666](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L666) | “linear decreasing in x²” | “decreasing linearly with x²” |
| [782](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L782) | Ranges of theorem and proposition numbers span a shared numbering sequence and multiple result types. | List the intended results explicitly, or refer to the relevant sections followed by the specific endpoint result. |
| [809](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L809) | “Q = min” | State “Throughout the table, Q ≤ M” in the caption and remove this shorthand. |
| [917](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L917) | “strip (λ₁, μ₁) = …” | “factor out the greatest common divisor by writing (λ₁, μ₁) = …” |
| [1007](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1007) | “the unreoriented symbolic denominator” | “the denominator before this sign adjustment” |
| [1118](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1118) | “the exact respective onsets” | “the corresponding threshold values” |
| [1209](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1209) | “First order, polynomial coefficients:” | “The first-order recurrence for (pⱼ, dⱼ) is” |
| [1220](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1220), [1236](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1236), [1544](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1544) | “tan-addition” | “the tangent addition formula,” with the surrounding grammar adjusted |
| [1303](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1303) | “whose gap window is real” before the term is explained | Define the window and its nonempty/real-endpoint condition before using the phrase. |
| [1389](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1389) | “finite-state implication” | Name the specific implication or alternatives just checked; the later projective-state discussion makes “finite-state” potentially confusing. |
| [1391](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1391) | “is linear decreasing in X” | “decreases linearly with X” |
| [1550](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1550) | “coefficients nonnegative, so positivity is inspection” | “coefficients nonnegative, so nonnegativity follows by inspecting the coefficients” |
| [1565](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1565) | “cross-checked against every binomial coefficient” | “checked against the defining binomial convolution for every coefficient” — this matches the finite-verification description earlier in the paper. |
| [1641](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1641) | “a mesh … has minimum m_L for L” | “let m_L be the minimum of L over the mesh points” — make the sampled minimum explicit. |
| [1743](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1743) | “distribution mirror” | “distribution site,” alongside the exact version link |
| [1945](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1945) | New notation pₛ⁽Q⁾ in a recursion | Define the notation and state which parameter is held fixed when Q changes. |
| [1947](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1947) | “a second, asymptotics-free proof” | Describe the desired uniformity in Q directly. The current proof already disclaims unquantified asymptotic estimates, so this phrase does little to identify the proposed advance. |
| [1956](https://github.com/skypher/kraw/blob/7955273411dd42d6102d0e8858da869b6fa8f204/paper/krawtchouk_turan_positivity.tex#L1956) | “On the top half … ≥ 1” | “Corollary 1.2 gives Tur(s) ≥ 1 for every 0 ≤ s ≤ D.” The open question can recall the full stated conclusion. |

The AI-use disclosure on page 29 is clear about both the role of the tool and the author's responsibility. Retain that substantive disclosure. The internal model identifier and reasoning-setting detail are optional; removing them would shorten the paragraph without changing its meaning. This review does not assess the historical accuracy of that disclosure.

**5. Bibliography audit**

Double-check: all 22 bibliography keys are cited, none is duplicated, and the generated bibliography contains 22 entries. I compared the 18 DOI-bearing entries against the returned Crossref records and checked the other four against book records, publisher material, or arXiv metadata. I inspected the printed bibliography as well as its source.

I found no author/title/year/volume/issue/pagination discrepancy in those metadata comparisons. The citation corrections in items 1.1 and 1.2 concern where and how the works are cited. Matching bibliographic metadata does not certify every characterization of a cited theorem.

| Citation | Publication details checked | Editorial result / source |
|---|---|---|
| [AK22] Ayyer–Kumari | *J. Algebra* 609 (2022), 437–483 | Metadata matches; correct attribution of Theorem 2.5 as above. [DOI](https://doi.org/10.1016/j.jalgebra.2022.06.015) |
| [BI97] Bustoz–Ismail | *Int. J. Math. Math. Sci.* 20(1) (1997), 1–7 | Metadata matches. [DOI](https://doi.org/10.1155/S016117129700001X) |
| [BS09] Berg–Szwarc | *J. Approx. Theory* 161(1) (2009), 127–141 | Metadata matches; the DOI's 2008 component is not the issue year. [DOI](https://doi.org/10.1016/j.jat.2008.08.010) |
| [CC89] Craven–Csordas | *Pacific J. Math.* 136(2) (1989), 241–260 | Metadata matches. [DOI](https://doi.org/10.2140/pjm.1989.136.241) |
| [Del73] Delsarte | *Philips Research Reports Supplements*, no. 10, Eindhoven, 1973 | Title, series, year, and publisher agree with the [original title/copyright page](https://users.wpi.edu/~martin/RESEARCH/philips.pdf). |
| [Kah26] Kahler | arXiv:2605.05180v1, 2026 | Author, title, identifier, and version match [arXiv](https://arxiv.org/abs/2605.05180). The spelling **Kahler** is correct; do not add an umlaut. |
| [Kar25] Karmakar | *Proc. Indian Acad. Sci. Math. Sci.* 135(2) (2025), article 41 | Metadata matches. Consider printing “Article 41” to distinguish the article number from a page. [Publisher](https://link.springer.com/article/10.1007/s12044-025-00847-0) |
| [KL96] Krasikov–Litsyn | *J. Combin. Theory Ser. A* 74(1) (1996), 71–99 | Metadata matches. [DOI](https://doi.org/10.1006/jcta.1996.0038) |
| [KLS10] Koekoek–Lesky–Swarttouw | *Hypergeometric Orthogonal Polynomials and Their q-Analogues*, Springer, 2010 | Metadata matches. [DOI](https://doi.org/10.1007/978-3-642-05014-5) |
| [Kra01] Krasikov | *Codes and Association Schemes*, DIMACS 56 (2001), 193–198 | Chapter metadata matches; the [AMS volume record](https://bookstore.ams.org/dimacs-56/) identifies Barg and Litsyn as editors. [DOI](https://doi.org/10.1090/dimacs/056/15) |
| [Kra03] Krasikov | *Anal. Appl.* 1(2) (2003), 189–197 | Metadata matches; retain 189–197. [DOI](https://doi.org/10.1142/S0219530503000120) |
| [Kra05] Krasikov | *Methods Appl. Anal.* 12(1) (2005), 75–88 | Metadata matches. [DOI](https://doi.org/10.4310/MAA.2005.v12.n1.a5) |
| [Kra11] Krasikov | *J. Approx. Theory* 163(9) (2011), 1269–1299 | Metadata matches. [DOI](https://doi.org/10.1016/j.jat.2011.04.004) |
| [Lev95] Levenshtein | *IEEE Trans. Inform. Theory* 41(5) (1995), 1303–1321 | Metadata matches. [DOI](https://doi.org/10.1109/18.412678) |
| [LW00] Li–Wong | *J. Approx. Theory* 106(1) (2000), 155–184 | Metadata matches. [DOI](https://doi.org/10.1006/jath.2000.3474) |
| [Mac95] Macdonald | *Symmetric Functions and Hall Polynomials*, second edition, Oxford, 1995 | Metadata matches; correct the character locator as above. [Publisher](https://academic.oup.com/book/52932) |
| [MS77] MacWilliams–Sloane | *The Theory of Error-Correcting Codes*, North-Holland Mathematical Library 16, 1977 | Book metadata matches; retain the 1977 original-publication year. [Publisher preview](https://api.pageplace.de/preview/DT0400.9780080954233_A23544044/preview-9780080954233_A23544044.pdf) |
| [RS98] Reiner–Stanton | *J. Algebraic Combin.* 7(1) (1998), 91–107 | Metadata matches. [DOI](https://doi.org/10.1023/A:1008623312887) |
| [Sze48] Szegő | *Bull. Amer. Math. Soc.* 54(4) (1948), 401–405 | Metadata matches; see the historical-wording recommendation above. [DOI](https://doi.org/10.1090/S0002-9904-1948-09017-6) |
| [Sze75] Szegő | *Orthogonal Polynomials*, fourth edition, AMS Colloquium Publications 23, 1975 | Edition, series, year, and publisher match [NIST's bibliography](https://dlmf.nist.gov/bib/S). |
| [Szw98] Szwarc | *Harmonic Analysis and Hypergroups*, 1998, 165–182 | Chapter metadata and the six listed editors match the [publisher record](https://link.springer.com/chapter/10.1007/978-0-8176-4348-5_11). The 2007 arXiv identifier is compatible with the 1998 publication. |
| [Szw21] Szwarc | *J. Approx. Theory* 270 (2021), article 105618 | Metadata matches. Consider printing “Article 105618.” The internal key `szwarc20` need not match the publication year. [DOI](https://doi.org/10.1016/j.jat.2021.105618) |

The bibliography's journal abbreviations, author-name formatting, repeated-author dashes, and alphabetic labels are acceptable. There is no benefit in rewriting these solely for cosmetic uniformity before posting.

**Add a citation for SymPy.** The article describes its use repeatedly, and the reference list currently lacks its standard software paper. The official recommendation is Meurer et al., “SymPy: symbolic computing in Python,” *PeerJ Computer Science* 3 (2017), e103, DOI 10.7717/peerj-cs.103. The [official citation page](https://docs.sympy.org/latest/citing.html) supplies the full BibTeX entry. Cite this paper alongside the explicit SymPy 1.12 environment declaration; the documented computation version should remain the version actually used.

**Locator-check scope.** Macdonald's cited determinant/character locations and the attribution surrounding Ayyer–Kumari's Theorem 2.5 were directly inspected. The cited Theorem 5 and equation (17) of Krasikov, and Theorem 4.1 of Karmakar, occur in accessible preprints; I have not certified their numbering against the final publisher PDFs. Bustoz–Ismail's equation (2.4) and KLS §9.11 were not independently checked in the complete cited editions during this review. No claim that every mathematical use of the literature has been checked is intended.

**6. Proposed abstract**

This replacement preserves the manuscript's stated conclusions and account of computer assistance. It is an editorial proposal, not an endorsement of those conclusions.

> Let M and Q be nonnegative integers, set D = M + Q, and define pₛ = [wˢ](1 + w)ᴹ(1 − w)^Q, with pₛ = 0 outside 0 ≤ s ≤ D. These are the binary Krawtchouk values Kₛ(Q;D) in the generating-function normalization. We prove that the Turán determinants Tur(s) = pₛ² − pₛ₋₁pₛ₊₁ satisfy Tur(s) ≥ Tur(s + 1) for ⌈D/2⌉ ≤ s ≤ D. Consequently, the determinants form a symmetric weakly unimodal sequence and are at least 1 for every 0 ≤ s ≤ D. By the dual Jacobi–Trudi identity, they are also values of rectangular Schur functions at an alphabet of M ones and Q minus ones; for D ≥ 1, this gives positivity and unimodality for a family of general linear character values at involutions. The proof combines recurrence comparisons in infinite regions, exact symbolic certificates for finitely many parameter families, and an exhaustive integer-arithmetic computation for the remaining finite cases. Source programs and deterministic replay logs are available in the accompanying repository.

**7. Document-production checks and arXiv preparation**

Double-check: I read the saved final LaTeX log, compared PDF hashes, inspected the font listing and bookmark outline, and reviewed renderings of every page.

| Check | Result for the reviewed version |
|---|---|
| Temporary-directory build | The complete `make paper` build succeeded. |
| Final LaTeX log | No warnings, overfull/underfull boxes, or unresolved-reference messages found. |
| Rebuilt PDF versus supplied PDF | Byte-for-byte identical SHA-256: `eb0a00b4994537111cde37ea35fbd61e8af4735f3dba5502f6ea4fed02ee4f45`. |
| PDF size and format | 30 pages; PDF 1.5; US Letter. |
| Fonts | All listed fonts embedded and subsetted; no Type 3 fonts. |
| Source references | No unresolved literal reference targets or duplicate labels found. Macro placeholders were excluded from this check. |
| Bibliography | 22 entries, all cited; DOI visibility issue described above. |
| Visual inspection | No obvious clipping, collisions, or missing glyphs found. The specific float/title/table improvements are listed above. |

These results concern the existing version and local toolchain. Rebuild the final edited source and inspect the arXiv-generated PDF at submission.

Current arXiv instructions support uploading `.bib` files and running BibTeX. A pre-generated `.bbl` is optional; if supplied, it takes precedence and must match the main source's basename. Consequently, regenerate it after bibliography changes rather than submitting a stale one. This is especially relevant when adding visible DOIs or a software citation. See [arXiv's current TeX submission instructions](https://info.arxiv.org/help/submit_tex.html).

Submit the paper's TeX/bibliography inputs and any actual dependencies, not the full development checkout. Exclude this editorial report and build intermediates from the paper-source upload. The current figure is defined within the TeX source. Keep the title, author, abstract, version, and availability links consistent between the final PDF, release, and submission metadata. arXiv's instructions also explain which generated files should be omitted and require inspection of its processed PDF. [Submission guidance](https://info.arxiv.org/help/submit_tex.html).

The priority order is: citation corrections; abstract and definite wording edits; file/release identification; bibliography links; figure placement; then optional compression of the introduction and verification discussion.
