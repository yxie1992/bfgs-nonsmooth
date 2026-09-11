# Source-only public audit package

The public package excludes five transient supplemental `.olean` objects from
its artifact manifest. The compiler created them in the recorded fresh run;
they are reproducible outputs, not source inputs or required delivered evidence.
The fresh command logs, exact copied sources, declaration inventories and input
hashes remain unchanged. A rerun compiles all five objects anew in its fresh
output directory. The audit manifest binds only files actually delivered.

This packaging correction does not change a Lean declaration, audit driver,
compiler result, theorem count, axiom set or dependency edge.
