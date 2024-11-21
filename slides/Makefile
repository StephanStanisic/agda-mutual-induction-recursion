
default:slides.pdf

verbose:slides.md
	pandoc -t beamer slides.md -o slides.pdf --slide-level=2 --pdf-engine=xelatex --verbose --template include/beamer-template.tex


slides.pdf:slides.md
	pandoc -t beamer slides.md -o slides.pdf --slide-level=2 --pdf-engine=xelatex --template include/beamer-template.tex

tex:slides.md
	pandoc -t beamer slides.md -o slides.tex --slide-level=2 --pdf-engine=xelatex --verbose --template include/beamer-template.tex

clean:
	rm *.aux *.log *.nav *.out *.snm *.toc *.vrb || true
