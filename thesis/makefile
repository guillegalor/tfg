main.pdf: main.tex titlepage.tex src/Maths/*
	pdflatex --shell-escape main.tex
	bibtex main
	pdflatex --shell-escape main.tex
	pdflatex --shell-escape main.tex

clean:
	rm main.pdf *.aux *.blg *.log *.bbl *.toc *.out
