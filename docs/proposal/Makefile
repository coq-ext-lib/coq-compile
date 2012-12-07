compiler.pdf: compiler.tex bib.bib
	@ pdflatex compiler
	@ bibtex compiler
	@ pdflatex compiler
	@ pdflatex compiler

proposal.pdf: proposal.tex bib.bib
	@ pdflatex proposal
	@ bibtex proposal
	@ pdflatex proposal
	@ pdflatex proposal

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.pdf *.synctex.gz
