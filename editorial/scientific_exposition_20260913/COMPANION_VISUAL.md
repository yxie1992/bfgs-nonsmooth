# Final companion visual check

The 107-page companion passes this bounded final visual check. The two footer definitions in `companion/preamble.tex` were corrected from 12 to 13 September 2026, matching the title page. Only the companion was rebuilt. Its final SHA-256 is `3566ec4fe7cd003f04f2adab81820d404cbfd588498891539d9471cb0798d042`.

The exact prior PDF (`9dd08e155e1d4dccb64b4a29898eb0a8e60a37a1039484317826e9d2c94c6029`) and its 107 canonical page PNGs were preserved before the edit. Both renderings use 100 dpi and 827×1170 RGB pixels. Every fixed body crop `[0,0,827,1095]` is exactly equal, pixel for pixel. All full-page pixel changes occur solely in one of two six-by-ten-pixel boxes at y 1107–1117: the changed date digit in the normal or plain-page footer. Page 1 is wholly unchanged.

The root agent had already confirmed visual review of all nine body pages changed by this exposition revision; the other body pages retain the prior completed review through their existing equality checks. This component carries body approval only through the new exact cropped-pixel equality. It does not claim that this subagent freshly inspected all 107 full pages.

All 107 excluded footer bands, including the empty title-page band, were actually viewed across nine enlarged strip sheets. Every displayed date is 13 September 2026; page numbers and both footer styles remain aligned and unobstructed. Full PDF pages 1, 10, 53, 94 and 104 were additionally viewed. No clipping, overlap or body/footer collision was found. Canonical companion contact sheets were regenerated.

The companion-only latexmk build and Poppler render both succeeded. The final log has no overfull boxes or LaTeX warnings; its three inherited underfull notices remain. Exact per-page PNG, body and footer hashes, full difference bounding boxes, actual build output, strip hashes, and five full-page inspection records are in `COMPANION_VISUAL.json`. The shared render manifest was updated only for the companion; the article entry was preserved.

Unrelated duplicate `page-… 2.png` files were retained. The comparison explicitly selects the 107 canonical `page-NNN.png` files, as recorded in the prior manifest. No metadata release, commit, push, new formal audit or PDF-operation marker was performed.
