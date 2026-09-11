# Literal semialgebraic paths: delivered scope

The seven reviewed scopes contain33 source files,152 actual declarations (including generated structure declarations),and16 exact target pairs. Source statements and proof bodies are byte-preserved; only recorded import qualification changes.

Run `bash audit/verify_semialgebraic_path_completion.sh` from the project. It checks import-only provenance and frozen public owner/peer evidence,then freshly builds the33 delivered modules and audits all152 transitive-axiom reports and16 strict target equalities. It needs only delivered files and the pinned project/toolchain; historical scratch paths in the manifest are provenance labels,not runtime inputs.

The actual scope includes restricted semialgebraic path graphs,explicit smooth path constructors,a finite semialgebraic path cover derived from semialgebraicity,scalar/vector/composed-objective smoothness outside derived finite exceptional sets,actual continuous-semialgebraic path-class equivalence,and affine-critical path constancy. Public source/independent reviews remain verbatim under `audit/semialgebraic_path_completion_reviews/`.

Manifest:`audit/semialgebraic_path_completion_declarations.json`. Driver:`audit/SemialgebraicPathCompletionAudit.lean`. Fresh build/axiom/validation outputs use prefix`semialgebraic_path_completion`. The copy-validation log records only import/provenance checks;it does not claim the later delivered compiler audit already ran. Root imports,central Audit,checker and release metadata are outside this integration script.
