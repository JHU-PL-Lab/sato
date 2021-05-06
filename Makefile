.PHONY: all ddse ddpa sato clean repl sandbox test translator benchmark

all: sato ddse translator

sato:
	dune build
	dune build src/sato-main/sato.exe
	rm -f sato
	ln -s _build/default/src/sato-main/sato.exe sato 

translator:
	dune build
	dune build src/translator-main/translator.exe
	rm -f translator
	ln -s _build/default/src/translator-main/translator.exe translator

ddpa:
	dune build
	dune build src/toploop-main/ddpa_toploop.exe
	rm -f ddpa_toploop
	ln -s _build/default/src/toploop-main/ddpa_toploop.exe ddpa_toploop

sandbox:
	dune build test/sandbox/sandbox.exe
	rm -f sandbox
	ln -s _build/default/test/sandbox/sandbox.exe sandbox

repl:
	dune utop src -- -require pdr-programming

test:
	dune build test/test.exe
	_build/default/test/test.exe

clean:
	dune clean
	rm -f ddpa_toploop
	rm -f translator
	rm -f sandbox
	rm -f test_generator
	rm -f sato

benchmark:
	dune exec benchmark-test-generation/benchmark.exe
