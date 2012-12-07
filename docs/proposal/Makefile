proposal.pdf: proposal.tex bib.bib
	@ pdflatex proposal
	@ bibtex proposal
	@ pdflatex proposal
	@ pdflatex proposal

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.pdf *.synctex.gz