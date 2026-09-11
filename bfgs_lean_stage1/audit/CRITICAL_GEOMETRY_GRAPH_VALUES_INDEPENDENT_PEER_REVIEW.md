# Independent review: finite critical graph values

PASS. All four declarations of the frozen `FiniteCriticalGraphValues.lean` were reviewed and freshly compiled into the peer object directory. Four actual type and transitive-axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Independently restated contracts for both mathematical conclusions passed strict definitional equality. The primary source plus six relevant dependency source hashes are unchanged.

The finite-set enumeration uses the actual `Finset.equivFin` equivalence, preserves membership in the supplied cover, and proves literal union equality. It includes an empty family. The graph-image identity uses the actual objective lift and both defining coordinates of `affineCriticalGraph`; it introduces no smoothness premise on the objective.

For `finite_critical_values_of_smooth_graph_cover`, every cover piece is proved to lie in the actual lifted critical graph. Its supplied piecewise-smooth path projects to a path on which both the position and actual objective composition are differentiable away from finitely many times. The convex supporting-vector path theorem makes the last coordinate constant on that piece. The actual critical-value image is therefore a finite union of subsingletons. There is no assumed objective differentiability, finite critical-value premise, or assumed constant graph height.

For `finite_semialgebraic_components_of_smooth_cover`, each supplied smooth-path-connected piece is preconnected, including empty pieces. The already reviewed finite-preconnected-cover and whole-component-union theorems yield finitely many actual connected components and semialgebraicity of every actual component. No closed, open, disjoint, or nonempty-piece hypothesis was added.

Both statements explicitly retain an actual finite cover premise. They are correct conditional assembly results and do not by themselves derive a global smooth finite cover for arbitrary semialgebraic sets. The component conclusion concerns ordinary connected components; it does not assert that each ordinary component is connected by piecewise-smooth paths. That stronger identification is neither used nor hidden.

Evidence: `GraphValuesPeerAudit.lean`, `graph_values_peer_source_hashes.json`, `graph_values_peer_build.log`, `graph_values_peer_axioms_contracts.log`, and `graph_values_peer_validation.log`. Sources were not modified.
