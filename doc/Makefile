STDLIB=~/languages/agda/libs/agda-stdlib-0.12/src/
SED=sed
PAPER=models
AUXILIARY=usual
SLIDES=2017-01-17


all: finish

prepare:
	mkdir -p latex/
	rm -f latex/$(SLIDES).*
	cp *.tex *.cls *.bib *.sed *.config latex/

paper: prepare
	./lagda2tex motivation.lagda
	./lagda2tex $(PAPER).lagda
	cd latex && ${SED} -f rules.sed -f rules2.sed -i $(PAPER).tex && ${SED} -f rules-motivation.sed -f rules.sed -f rules2.sed -i motivation.tex && \
	latexmk -bibtex -pdf -e '$$pdflatex=q/xelatex %O %S/' $(PAPER).tex && cd ..

auxiliary:
	./lagda2tex $(AUXILIARY).lagda
	sed -f rulesUsual.sed -f rules.sed -f rules2.sed -i latex/$(AUXILIARY).tex

slides: prepare auxiliary
	cd latex && ${SED} -f rules.sed -f rules2.sed -i $(SLIDES).tex -i $(AUXILIARY).tex $(PAPER).tex && \
	latexmk -bibtex -pdf -e '$$pdflatex=q/xelatex %O %S/' $(SLIDES).tex
	ln -sf latex/${SLIDES}.pdf .

finish: paper auxiliary slides
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1
clean:
	rm -f *.agdai
	rm -rf latex/
