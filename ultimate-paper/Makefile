file    = paper
lhs2tex = lhs2TeX --poly

$(file).pdf: $(file).ltx references.bib custom.fmt
	$(lhs2tex) $(file).ltx > $(file).tex
	latexmk -pdf $(file).tex

crop:
	pdftk $(file).pdf cat 1-12 output main.pdf
	pdftk $(file).pdf cat 13-19 output appendices.pdf

clean:
	rm -f $(file).tex $(file).log $(file).pdf $(file).aux $(file).bbl $(file).blg $(file).fdb* $(file).fls