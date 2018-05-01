file    = paper
lhs2tex = lhs2TeX --poly

$(file).pdf: $(file).ltx references.bib
	$(lhs2tex) $(file).ltx > $(file).tex
	latexmk -pdf $(file).tex

clean:
	rm -f $(file).tex $(file).log $(file).pdf $(file).aux $(file).bbl $(file).blg $(file).fdb* $(file).fls