
TGT=index
LATEX=pdflatex -shell-escape -output-directory=dist

## No need to lose our tex files
.PRECIOUS: %.tex

%.tex: %.lhs
	lhs2TeX -o $@ $< 

default : src/$(TGT).tex
	@mkdir -p dist
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	$(LATEX) src/$(TGT).tex 

dist/$(TGT).aux: default

bib: references.bib dist/$(TGT).aux
	bibtex dist/$(TGT).aux
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	$(LATEX) src/$(TGT).tex

clean :
	cd dist && rm -rf * && cd ..
