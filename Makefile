.PHONY: paper clean-paper

paper:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=../tex-build source-revised.tex

clean-paper:
	cd paper && latexmk -C -outdir=../tex-build source-revised.tex
