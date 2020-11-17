.PHONY: all ddse sato clean repl sandbox test benchmark

all:
	dune build
	dune build src/toploop-main/ddpa_toploop.exe
	dune build src/test-generation-main/test_generator.exe
	dune build src/translator-main/translator.exe
	dune build src/type-checker-main/type_checker.exe
	dune build src/type-verifier-main/type_verifier.exe
	rm -f ddpa_toploop
	rm -f translator
	rm -f test_generator
	rm -f type_checker
	rm -f type_verifier
	ln -s _build/default/src/toploop-main/ddpa_toploop.exe ddpa_toploop
	ln -s _build/default/src/test-generation-main/test_generator.exe test_generator
	ln -s _build/default/src/translator-main/translator.exe translator
	ln -s _build/default/src/type-checker-main/type_checker.exe type_checker
	ln -s _build/default/src/type-verifier-main/type_verifier.exe type_verifier

ddse:
	dune build
	dune build src/test-generation-main/test_generator.exe
	rm -f test_generator
	ln -s _build/default/src/test-generation-main/test_generator.exe test_generator

sato:
	dune build
	dune build src/type-checker-main/type_checker.exe
	dune build src/type-checker-main/type_verifier.exe
	rm -f type_checker
	rm -f type_verifier
	ln -s _build/default/src/type-checker-main/type_checker.exe type_checker
	ln -s _build/default/src/type-verifier-main/type_verifier.exe type_verifier

sandbox:
	dune build test/sandbox/sandbox.exe
	rm -f sandbox
	ln -s _build/default/test/sandbox/sandbox.exe sandbox

repl:
	dune utop src -- -require pdr-programming

test:
	dune build test/unittest/test.exe
	_build/default/test/unittest/test.exe

clean:
	dune clean
	rm -f ddpa_toploop
	rm -f translator
	rm -f sandbox
	rm -f test_generator
	rm -f type_checker
	rm -f type_verifier

benchmark:
	dune exec benchmark-test-generation/benchmark.exe
