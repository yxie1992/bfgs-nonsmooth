# What in the delivered article prompted this revision

Source: BFGS_paper_companion_sources.zip, article under BFGS-non-smooth/paper/. These are source inspections, not a new mathematical or Lean audit.

## 1. Research context arrives after the contribution statements

`sections/introduction.tex` starts immediately with the finite-polyhedral-versus-four-smooth-formulas contrast. It then inserts positive_partition, negative_upper and negative_lower, and the regularity table. The main primary-literature account begins only under the later related-work subsection.

The contrast is valid but premature. The reader should first see the recognized nonsmooth-BFGS problem and the precise gap in preceding work. A later related-work subsection cannot by itself establish the motivation for already stated theorems.

## 2. A compelling benchmark result is buried in applications

`sections/positive.tex`, lines 177–185 in the delivered archive, gives the whole-sequence u^2+|v| conclusion and explicitly compares it to Guo--Lewis Corollary 4.4. This is one of the clearest demonstrations of research significance, but it appears as an application paragraph after the proof of the centered theorem.

Promote it into the introduction's prior/current comparison and a named corollary. Preserve the family proof; do not replace it with a new isolated calculation.

## 3. Generality is advertised but its payoff is largely delegated

`sections/beyond.tex` explicitly says its three geometric extensions are not among the article's independently established results, then gives a scope catalogue. It also delegates the homogeneous noncompact and quantitative theory.

Some delegation is appropriate. But the article must prove a substantial set of the positive achievements it uses to establish significance, and demonstrate why a headline general certificate is more useful than its radial specialization. This is a selection/argument problem, not something solved by adding more orientation prose to that section.

## 4. Attribution is technically careful but sometimes rhetorically defensive

The introduction credits classical algebra and says it does not attribute determinant, trace or AM–GM tools to the current work. Such qualifications are legitimate in the audit. In the paper, affirmative lineage is clearer: name the classical approach and explain exactly how the adjacent-degree hierarchy changes what can be deduced.

## 5. The revision needed is architectural

The earlier review remains useful for scaling explanations, figures, notation and proof completeness. But balancing the numbers of positive and negative theorems does not create a research story. The next pass must recast the introduction, selected main results, transitions, proof motivation and conclusion together.
