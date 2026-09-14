.PHONY: all paper check cubic nodes review-check certificate reduced manifest arxiv-bundle clean lean-data lean-verify
all: paper
paper:
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
check:
	python3 scripts/check_data.py
cubic:
	python3 scripts/check_cubic_maps.py
nodes:
	python3 scripts/check_nodes_modp.py --out certificate/results/nodes_modp_check.json
review-check:
	python3 scripts/check_review_evidence.py --out certificate/results/review_evidence_check.json
certificate:
	python3 scripts/run_certificate.py

reduced:
	python3 scripts/run_reduced_presentations.py --workers 6
manifest:
	python3 scripts/write_manifest.py
lean-data:
	python3 lean/tools/generate.py
lean-verify:
	cd lean && python3 verify.py
arxiv-bundle:
	python3 scripts/build_arxiv_bundle.py
clean:
	latexmk -c main.tex
