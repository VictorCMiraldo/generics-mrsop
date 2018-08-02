file     = paper
appendix = appendices
lhs2tex  = lhs2TeX --poly

all: $(file).pdf $(appendix).pdf

$(file).pdf: $(file).ltx references.bib custom.fmt
	$(lhs2tex) $(file).ltx > $(file).tex
	latexmk -pdf $(file).tex

$(appendix).pdf: $(appendix).ltx references.bib custom.fmt
	$(lhs2tex) $(appendix).ltx > $(appendix).tex
	latexmk -pdf $(appendix).tex

clean:
	rm -f $(file).tex $(file).log $(file).pdf $(file).aux $(file).bbl $(file).blg $(file).fdb* $(file).fls
	rm -f $(appendix).tex $(appendix).log $(appendix).pdf $(appendix).aux $(appendix).bbl $(appendix).blg $(appendix).fdb* $(appendix).fls