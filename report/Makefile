all: report.pdf

report.pdf: report.tex figures.tex introduction.tex related.tex btrees.tex model.tex verif.tex bugs.tex spec.tex conclusion.tex ../bib/btrees.bib
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
