.PHONY: all check doc serve clean
all: check doc

check:
	dune build

doc:
	alectryon \
		--cache-directory _alectryon \
		--output-directory html \
		--frontend coq+rst \
		--coq-driver sertop \
		--webpage-style windowed \
		-Q _build/default/theories OGS \
		theories/**/*.v

serve:
	python3 -m http.server -d html


clean:
	rm -rf _build _alectryon html
