all: compile

compile:
	pdflatex --shell-escape thesis.tex
	bibtex thesis
	pdflatex --shell-escape thesis.tex
	pdflatex --shell-escape thesis.tex

clean:
	find . -name "*.aux" -type f -delete
	rm -f thesis.toc thesis.out thesis.lot thesis.log thesis.lof thesis.ind thesis.ilg thesis.fls thesis.fdb_latexmk thesis.brf thesis.blg thesis.bbl thesis.idx
