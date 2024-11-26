
default:slides.pdf

slides.pdf:slides.md
	pandoc -t beamer slides.md -o slides.pdf --slide-level=2 --pdf-engine=lualatex --template include/beamer-template.tex

clean:
	rm slides.!(md) || true
