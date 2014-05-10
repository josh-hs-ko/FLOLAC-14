lhs2TeX = /Users/joshko/Library/Haskell/bin/lhs2TeX

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

exam:
	$(lhs2TeX) exam.tex -o exam\'.tex
	xelatex -jobname exam exam\'

