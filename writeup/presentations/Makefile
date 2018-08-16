## Target of the makefile:
TARGET=tyde2018.pdf haskell2018.pdf

## Oracle Template dependencies
UU_DEPS=tex/latex/beamerthemeuucs.sty \
        tex/latex/agda.sty \
	tex/latex/img/uulogo.pdf \
	tex/latex/img/uueduc.jpg

all: $(TARGET) clean

uu_theme: $(UU_DEPS)

.PRECIOUS: %.tex

## Makes all the pdfs; rebuild them if we change only the theme.
%.pdf: %.tex uu_theme
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	xelatex $<

%.tex: %.lhs
	lhs2TeX --poly $< -o $@

clean: 
	rm -f *.aux
	rm -f *.log
	rm -f *.nav
	rm -f *.out
	rm -f *.snm
	rm -f *.toc

cleanall: clean
	rm *.pdf
	rm *.tex
