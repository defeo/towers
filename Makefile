towers.pdf: towers.tex creat.pdf
	pdflatex towers
	bibtex towers
	pdflatex towers
	pdflatex towers

creat.eps: creat.gp bench.dat
	gnuplot creat.gp

creat.pdf: creat.eps
	epstopdf creat.eps
