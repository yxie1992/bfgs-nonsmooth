# Overbroad warning classifier rejected package metadata

The LaTeX command succeeded. The initial broad case-insensitive warning-word
filter rejected the ordinary package metadata line describing infwarerr as
providing info/warning/error messages. The run was correctly marked FAIL rather
than retaining an old PASS. The final classifier recognizes actual LaTeX, font,
package, class and pdfTeX warning prefixes, together with overflow, missing glyph
and unresolved-reference messages. The final renderer is rerun after this
classification correction. No mathematical source or Lean proof changed.
