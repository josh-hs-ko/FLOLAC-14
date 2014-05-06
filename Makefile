lhs2TeX = /Users/joshko/Library/Haskell/bin/lhs2TeX

lecture_1:
	$(lhs2TeX) lecture_1.tex -o lecture_1\'.tex
	xelatex -jobname lecture_1 lecture_1\'

exam:
	$(lhs2TeX) exam.tex -o exam\'.tex
	xelatex -jobname exam exam\'

