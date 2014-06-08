lhs2TeX = /Users/joshko/Library/Haskell/bin/lhs2TeX

all: 4up

lecture_1:
	$(lhs2TeX) lecture_1.tex -o lecture_1\'.tex
	xelatex -jobname lecture_1 lecture_1\'

lecture_2:
	$(lhs2TeX) lecture_2.tex -o lecture_2\'.tex
	xelatex -jobname lecture_2 lecture_2\'

lecture_3:
	$(lhs2TeX) lecture_3.tex -o lecture_3\'.tex
	xelatex -jobname lecture_3 lecture_3\'

lecture_4:
	$(lhs2TeX) lecture_4.tex -o lecture_4\'.tex
	xelatex -jobname lecture_4 lecture_4\'

lecture_4_partial.pdf: lecture_4.pdf
	pdfjam lecture_4.pdf 1-7,9-10,14-17 --fitpaper true --outfile lecture_4_partial.pdf

4up: lecture_1.pdf lecture_2.pdf lecture_3.pdf lecture_4_partial.pdf
	pdfjam --nup 2x2 --landscape --frame true --delta ".25cm .5cm" --scale .95 --suffix "4up" --batch lecture_1.pdf lecture_2.pdf lecture_3.pdf lecture_4_partial.pdf
	pdfjam lecture_1-4up.pdf lecture_2-4up.pdf lecture_3-4up.pdf lecture_4_partial-4up.pdf --fitpaper true --outfile lectures-4up.pdf
	pdf90 lectures-4up.pdf --outfile TT_lectures_4up.pdf
	rm -f *-4up.pdf

exam:
	$(lhs2TeX) exam.tex -o exam\'.tex
	xelatex -jobname exam exam\'

