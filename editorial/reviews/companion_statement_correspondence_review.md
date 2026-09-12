# Expanded companion statement correspondence

Reviewed the headings and source boundaries of all fourteen generated companion chapters. The earlier theorem-environment-only scan omitted three manually headed homogeneous theorems, the homogeneous affine-balance lemma, and both manually headed fixed-normal theorems. The new inventory indexes those six results with their exact heading anchors, source IDs and complete formal export lists.

The assembled register now has 40 named companion results, ten explicitly anchored inline results, 73 unnamed mathematical-result/proof bundles, and a separate classified register for all 172 source spans. The inline records distinguish fixed-reference energy, the conditional moving-frame criterion, three rate corollaries, two affine-geometric propositions, additional scalar regularity, and the full/tangential-curvature composite alternatives. A proof bundle is explicitly not counted as an additional atomic theorem.

Definitions and scope, execution evidence, conditional criteria, and open boundaries have separate status fields. In particular, H.span.6 retains its proved value-summary export while its higher-rank iterate question remains open; A.span.5 has no theorem exports and remains an unproved conjecture. The uniform local-basin and fixed-normal assumptions are recorded without merging the distinct interface theorems.

`editorial/companion_statement_inventory.py` is consumed by `editorial/assemble_claim_ledger.py`. Assembly checks that every stored full export list equals the complete exact source-span union and that every export exists in the canonical declaration index. A repeated assembly produced byte-identical JSON and HTML outputs. All 172 source IDs were compared directly with `companion/SOURCE_CORRESPONDENCE.json`; none is missing. This is correspondence/index validation, not a new Lean compiler or mathematical-proof claim.

`editorial/NOTATION_MAP.md` records shared algorithmic and geometric notation and the distinct scalar conventions. In particular, the lower-curvature article scalar psi_b is the companion chapter-13 varphi_b; its ratio, ramp width, node values and regularity differ from the upper-curvature scalar. The map does not conflate local symbols, matrix roles, or different Lean vector/norm representations.

No original research or Lean source was modified by this inventory task. Root assembly owns the final build and release audit.

## Reproducible validation output

```
Mapped 84 article records; 40 companion named results; 10 inline results; 73 unnamed mathematical spans; 172 complete classified source spans.
PASS: repeated assembly is byte-identical; every record preserves its complete source-export union; all 172 spans are present.
```

## Validated output hashes

- `editorial/CLAIM_LEDGER.json`: `14a7437871664efa2cd02796838a02a6f91f8f3680fe815e3aec573e5e5337b5`
- `companion/PROOF_CORRESPONDENCE.html`: `100bd9fc82ed13c0793f638e559273fb07c2c35ac86677e360f65baa7391ad37`
