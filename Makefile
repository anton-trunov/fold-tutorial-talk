slides: fold-slides.tex
	lualatex fold-slides.tex

show: slides
	open fold-slides.pdf

clean:
	rm -f *.log *.aux *.snm *.out *.nav *.synctex.* *.toc *.vrb

.PHONY: show clean
