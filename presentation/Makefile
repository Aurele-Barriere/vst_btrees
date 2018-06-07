all: pres

pres: pres.pdf

pres.pdf: cmds.tex style.tex figures.tex pres.tex lstcoq.sty
	pdflatex pres && pdflatex pres

clean:
	rm -rf *.aux *.bbl *.blg *.log *.nav *.out *.snm *.toc
