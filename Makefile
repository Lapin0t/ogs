.PHONY: all check doc serve clean
all: check doc

check:
	dune build

doc:
	alectryon \
		--cache-directory _alectryon \
		--output-directory docs \
		--frontend coq+rst \
		--coq-driver sertop \
		--webpage-style windowed \
		--long-line-threshold 100 \
		-Q _build/default/theories OGS \
		theories/*.v theories/**/*.v

serve:
	python3 -m http.server -d docs

docker-build:
	docker build -t coq-ogs:latest .

docker-save:
	docker image save coq-ogs:latest | gzip > docker_coq-ogs.tar.gz


clean:
	rm -rf _build _alectryon docs
