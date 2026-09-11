# Actual general polynomial projection: statement and source review

This scope closes the global projection prerequisite in the Module A plan, using the project's genuine `PolynomialFormula` and `IsSemialgebraic` definitions. The source report is unchanged. The relevant retained application is `affine_geometry.tex`, Proposition A:semialgebraic (lines 60–77). General projection alone does **not** prove finite affine-critical values or finite piecewise-C1 path decomposition; those remain separate downstream tasks.

The frozen manifest is `declarations.json`: eight owned source files, 51 explicit declarations plus the three constructor/projection reports for `FiniteSemialgebraicFunction`, 26 frozen scratch dependency source hashes, and five exact contracts. `verify.sh` rebuilds all 26 scratch dependencies into this scope's own dependency directory, then all eight owned modules, before printing actual declaration types, transitive axioms and ten strict source/wrapper comparisons. It does not modify other scopes' sources, objects, or logs. The actual fresh-run result belongs in `validation.log`; initial compiler passes are not substituted for that gate.

## Exact conclusions

`finiteSemialgebraic_rationalCauchyIndex p q` proves that the actual integer-valued function

`x ↦ rationalCauchyIndex (p.map (MvPolynomial.eval x)) (q.map (MvPolynomial.eval x))`

has finite range and that the fiber of every integer value has a genuine quantifier-free polynomial witness. Here `p,q : Polynomial (MvPolynomial σ ℝ)` are arbitrary and `[Finite σ]` is the only coordinate condition. `finiteSemialgebraic_tarskiQuery` proves the same for the actual signed sum on distinct real roots. No index function, query table, generic parameter locus, root count or degree preservation is assumed.

`polynomial_simultaneous_sign_projection` proves semialgebraicity of the parameters admitting one real scalar that realizes **all** signs in an arbitrary finite family of arbitrary-degree polynomials in `Option σ`. It has no nonzero, simple-root, fixed-degree, nonempty-family or bounded-fiber hypothesis. `polynomial_boolean_scalar_projection` extends this to every actual Boolean polynomial formula, including arbitrary negations. The common scalar witness is preserved through the whole finite sign pattern.

The primary final theorem is universe-polymorphic:

```lean
coordinate_projection_semialgebraic
    {σ : Type u} {τ : Type v} [Finite σ] [Finite τ]
    {S : Set ((σ ⊕ τ) → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic (coordinateProjection S)
```

`coordinateProjection` is the existing actual set `{x | ∃ y, Sum.elim x y ∈ S}`. `IsSemialgebraic` remains the existing existential witness of a quantifier-free `PolynomialFormula`; projection is not part of its definition. The named contracts instantiate coordinate types in `Type`, which includes the report's actual finite coordinate models; the underlying theorems also support arbitrary universes. The strict source checks instantiate polymorphic universe parameters before comparing complete types to these exact contracts.

## Proof chain and exceptional cases

1. `FiniteSemialgebraicFunctions` contains only finite-range/fiber closure properties. Constants, arbitrary postcomposition, pairs, finite sums, semialgebraic conditionals and finite selection are derived by actual finite unions and intersections of fibers. Polynomial sign fibers are equality/strict-inequality formulas. No projection property is introduced in this helper structure.

2. `PolynomialParameterSigns` proves actual specialized degree and leading sign have finite semialgebraic fibers. The induction is on the symbolic polynomial's natural degree. If its leading coefficient vanishes at the parameter, actual specialization is unchanged by erasing that leading term; the erased polynomial is either zero or has smaller degree. Otherwise the standard exact leading-coefficient/degree specialization theorems apply. Identically zero specializations and constant symbolic polynomials are included.

3. `SemialgebraicIndexQueries` uses actual symbolic positive pseudo-division. For a nonzero symbolic denominator `q`, it chooses the already proved identity

   `(C q.leadingCoeff)^(2*k) * p = q*Q + r`,

   where `r=0` or `r.natDegree<q.natDegree`. On the nonzero-leading-coefficient locus, the scalar multiplier is strictly positive. Actual rational-index invariance and reciprocity therefore give `index(p,q)=infinityVariation(r,q)-index(q,r)`. The zero remainder branch is derived too: both right-hand terms vanish. On the vanishing-leading-coefficient locus, the denominator is replaced by `eraseLead q` without changing the actual rational function. Both recursive branches strictly decrease the symbolic denominator degree unless they terminate at zero. Thus every exceptional degree drop is included in a finite proof, without selecting an actual parameter root or trusting a symbolic computation.

4. The actual endpoint term is semialgebraic because it is the proved parity/leading-sign function of the specialized product. The actual Tarski query equals the actual index of `q*p'` over `p`. For `p=0`, both finite-list quantities are zero, so the total equality is proved separately. This does **not** identify the zero polynomial's full real zero set with its empty library root list.

5. `ParameterSignQueries` applies the previously verified rational indicator inversion to finitely many actual Tarski queries. The subset of family members whose **specializations** are nonzero is itself finite-valued with semialgebraic fibers. On each such fiber, the product of those nonzero members is a fixed symbolic polynomial product. This is crucial: zero factors are removed after specialization, not merely once from the symbolic family. Its derivative is the actual derivative of that specialized product, by polynomial-map/derivative commutation.

6. `SimultaneousSignProjection` invokes the checked all-real sampling identity: roots of the nonzero-factor product, roots of its derivative, and the two actual coefficient/parity tail patterns. Bounded complementary intervals contain an actual derivative root by Rolle; signs are transported using the existing root-free sign-cell theorem. Repeated roots are treated distinctly, derivative zero gives an empty root-list query, constants and the empty family remain valid, and zero family members retain their required zero sign.

7. `BooleanPolynomialProjection` collects the actual finite atom-polynomial set of the original formula and enumerates every sign assignment on that set. Structural induction proves that equal atom signs give equal truth values under all conjunctions and negations. A sign assignment is retained precisely when the original Boolean structure evaluates true. The existential exchange is `(∃t,∃s,...) ↔ (∃s,∃t,...)`; separate witnesses for different atoms are never combined.

8. `GeneralCoordinateProjection` repeatedly eliminates one scalar by finite-type induction. It derives coordinate relabeling from polynomial substitution and explicitly proves the Option/Sum evaluation identity. The empty eliminated block and arbitrary equivalences of finite coordinate types are included. Internal `Fintype` instances are obtained from actual finiteness, not retained as additional mathematical assumptions.

## Trust and scope boundaries

Every arithmetic identity, recurrence, root sign, finite indicator expansion, set equality and termination argument is a Lean proof. Classical choice is used for standard finite witnesses and the proved pseudo-division existence theorem, not for an unproved mathematical oracle. No external root isolation, unchecked determinant/sign computation, custom mathematical assertion, placeholder proof, or changed semialgebraic definition enters the chain.

This is a mathematical existence theorem for quantifier-free polynomial witnesses, not a claimed executable optimized quantifier-elimination implementation or a complexity bound. It closes actual arbitrary-degree global finite-coordinate projection and therefore can discharge the existing explicit projection premises in the supporting-graph and affine-critical encodings. Finite smooth cylindrical cells, root delineability, finite path components and the final general affine-critical value-gap theorem are not inferred merely from this result and are not claimed by these five contracts.
