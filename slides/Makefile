default:slides.pdf

# slides.pdf:slides.md
# 	pandoc -t beamer slides.md -o slides.pdf --slide-level=2 --pdf-engine=lualatex --template include/beamer-template.tex

slides.pdf:slides.md
	pandoc --lua-filter minted.lua -t beamer slides.md -o slides.tex --slide-level=2 --pdf-engine=lualatex --no-highlight --pdf-engine-opt=-shell-escape --template include/beamer-template.tex
	sed -i 's/standout,fragile/standout/g' slides.tex
	lualatex -pdf -shell-escape -jobname=slides slides 

clean:
	bash -c "rm slides.!(md)" || true
