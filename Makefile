.PHONY: all build ocaml rust clean test

all: build

build: ocaml rust

ocaml:
	dune build

rust:
	cd enfflash && cargo build --release

clean:
	dune clean
	cd enfflash && cargo clean

test:
	python3 tests/test.py
