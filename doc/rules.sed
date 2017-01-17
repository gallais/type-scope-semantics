# Super- and subscripts.
## fix to make it work with Agda 2.4.2.4
s/\\textasciicircum\([^{]\)/\\textasciicircum\{\}\1/g
## Usual rules
s/‿\([^\}]*\)\\textasciicircum{}\([^\}]*\)/\^\{\\AgdaFontStyle\{\\scriptscriptstyle \2\}\}\_\{\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}/g
s/\\textasciicircum{}\([^.\}]*\)‿\([^\}]*\)/\^\{\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}\_\{\\AgdaFontStyle\{\\scriptscriptstyle \2\}\}/g
s/\\textasciicircum{}\([^.\}]*\)/\{\^\\AgdaFontStyle\{\\scriptscriptstyle\{\}\1\}\}/g
s/{\([^{.]*\)\({\^\\AgdaFontStyle{\\scriptscriptstyle{}[^\]*}\)/\{\{\1\}\2/g
s/‿\([^\}]*\)/\_\\AgdaFontStyle\{\\scriptscriptstyle \1\}/g

s/₀/\_\{\\scriptscriptstyle\{\}0\}/g
s/\^//g
# Operators
s/>>=/\\mathbin\{>\\!\\!>\\mkern-6.7mu=\}/g
s/>>/\\mathbin\{>\\!\\!>}/g
s/++/+\\!+/g

# Pointwise things
s/⟶/\\,\\dot\{→\}\\,/g
s/∙⊎/\\dot\{⊎\}/g
s/∙×/\\dot\{×\}/g

# Latex
s/^\\begin{code}/\\begin\{code\}\n\\\\/g
s/^\\end{code}/\\\\\\end\{code\}\n/g

# Set levels
s/L.zero//g
s/\\AgdaSymbol{(}[^:]*\\AgdaSymbol{:} \\AgdaPostulate{Level}\\AgdaSymbol{)} \\AgdaSymbol{→} //g
s/ \\AgdaBound{ℓ}//g
s/\\AgdaPrimitive{L.suc}//g
s/ \\AgdaPrimitive{⊔} //g
s/ \?\\AgdaBound{{ℓ}{[^{]*{[^{]*{}[^}]*}}}//g
s/\\AgdaSymbol{(}\\AgdaSymbol{)}//g
s/ \\AgdaSymbol{(}\\AgdaSymbol{))}/\\AgdaSymbol\{)\}/g
s/\\AgdaFunction{Model} \\AgdaSymbol{\\_}/\\AgdaFunction\{Model\}/g

# Implicit arguments
s/\\AgdaSymbol{λ} \\AgdaSymbol{\\{}\\AgdaBound{σ}\\AgdaSymbol{\\}} \\AgdaSymbol{\\{}\\AgdaBound{τ}\\AgdaSymbol{\\}} \\AgdaSymbol{→} //g
s/\\AgdaSymbol{\\{}\\AgdaBound{σ}\\AgdaSymbol{\\}} \\AgdaSymbol{\\{}\\AgdaBound{τ}\\AgdaSymbol{\\};}/\\AgdaSymbol{;}/g
s/\\AgdaSymbol{λ} \\AgdaSymbol{\\{}\\AgdaBound{σ}\\AgdaSymbol{\\}} \\AgdaSymbol{→} //g
s/\\AgdaSymbol{\\{}\\AgdaBound{σ}\\AgdaSymbol{\\}} //g
s/\\AgdaSymbol{\\{}.*\\AgdaSymbol{\\}}\([^=]*\)\\AgdaSymbol{=}/\1\\AgdaSymbol{=}/g
s/\\AgdaSymbol{\\{}.*\\AgdaSymbol{\\}}[^()→;]*\\AgdaSymbol{→} //g
s/\\AgdaSymbol{\\{}[^();]*\\AgdaSymbol{\\}}//g
s/\\AgdaSymbol{\\{}[^;]*\\AgdaSymbol{\\}}//g

# Hacks
s/`→/`\\!\\!→/g
s/`1/`\\!1/g
s/`2/`\\!2/g
s/𝓡/\\mathcal{R}/g

# Awful, Awful Hacks
s/\\AgdaSymbol{∀} \\AgdaBound{T}/\\AgdaSymbol{∀} \\AgdaSymbol{\\{}\\AgdaBound{Γ}\\AgdaSymbol{\\}} \\AgdaSymbol{→} \\AgdaBound{T}/
s/\\>\[13\]\\AgdaSymbol{(}\\AgdaBound{r} \\AgdaSymbol{:} \\<\[19\]%/\\>\[13\]\\AgdaSymbol{(}/
s/\\>\[19\]\\AgdaSymbol{∀} \\AgdaBound{inc}/\\AgdaSymbol{∀} \\AgdaBound{inc}/
s/\\AgdaFunction{CBN} \\AgdaSymbol{:}/\\AgdaFunction{CBX} \\AgdaSymbol{:}/
s/\\AgdaFunction{CBN} \\AgdaInductiveConstructor{`\\!1}/\\AgdaFunction{CBX} \\AgdaInductiveConstructor{`\\!1}/
s/\\AgdaFunction{CBN} \\AgdaInductiveConstructor{`\\!2}/\\AgdaFunction{CBX} \\AgdaInductiveConstructor{`\\!2}/
