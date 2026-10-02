.PHONY: paper clean-paper

paper:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=tex-build source-revised.tex

clean-paper:
	latexmk -C -outdir=tex-build source-revised.tex
