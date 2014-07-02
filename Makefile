lhs2TeX = /Users/joshko/Library/Haskell/bin/lhs2TeX

lectures = lecture_1 lecture_2 lecture_3 lecture_4

all: 4up

$(lectures):
	$(lhs2TeX) $@.tex -o $@\'.tex
	xelatex -jobname $@ $@\'

AC:
	$(lhs2TeX) AC.tex -o AC\'.tex
	xelatex -jobname AC AC\'

4up: $(lectures:=.pdf)
	pdfjam --nup 2x2 --landscape --frame true --delta ".25cm .5cm" --scale .95 --suffix "4up" --batch $(lectures:=.pdf)
	pdfjam $(lectures:=-4up.pdf) --fitpaper true --outfile lectures-4up.pdf
	pdf90 lectures-4up.pdf --outfile TT_lectures_4up.pdf
	rm -f *-4up.pdf

notes: $(lectures:=.pdf)
	pdfjam --nup 1x4 --frame true --suffix 'notes' --scale .95 --delta "0cm .25cm" --offset "-5.25cm 0cm" --batch $(lectures:=.pdf)

exam:
	$(lhs2TeX) exam.tex -o exam\'.tex
	xelatex -jobname exam exam\'

