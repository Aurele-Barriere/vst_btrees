all: report.pdf

report.pdf: btreecursor.sty types.c lstcoq.sty report.tex figures.tex introduction.tex related.tex btrees.tex model.tex verif.tex bugs.tex conclusion.tex appendix.tex ../bib/btrees.bib
	pdflatex report.tex
	bibtex report.aux
	pdflatex report.tex
	pdflatex report.tex

clean:
	-rm *.aux
	-rm *.bbl
	-rm *.log
	-rm *.blg
	-rm *.toc
	-rm report.pdf
