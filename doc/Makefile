STDLIB=~/repos/agda/std-lib/src/

PAPER=models
AUXILIARY=usual
SLIDES=slides


all: finish

prepare:
	mkdir -p latex/ && rm -f latex/$(SLIDES).* && cp *.tex *.cls *.bib *.sed *.config latex/

paper: prepare
	agda -i . -i $(STDLIB) --latex motivation.lagda && \
	agda -i . -i $(STDLIB) --latex $(PAPER).lagda && \
	cd latex && gsed -f rules.sed -f rules2.sed -i $(PAPER).tex && gsed -f rules-motivation.sed -f rules.sed -f rules2.sed -i motivation.tex && \
	latexmk -bibtex -pdf -e '$$pdflatex=q/xelatex %O %S/' $(PAPER).tex && cd ..

auxiliary:
	agda -i . -i $(STDLIB) --latex $(AUXILIARY).lagda
	sed -f rulesUsual.sed -f rules.sed -f rules2.sed -i latex/$(AUXILIARY).tex

slides: prepare auxiliary
	cd latex && sed -f rules.sed -f rules2.sed -i $(SLIDES).tex -i $(AUXILIARY).tex $(PAPER).tex && \
	latexmk -bibtex -pdf -e '$$pdflatex=q/xelatex %O %S/' $(SLIDES).tex && cd ..

finish: paper auxiliary slides
	xdotool search --class mupdf key --window %@ r > /dev/null 2>&1
clean:
	rm -f *.agdai
	rm -rf latex/
