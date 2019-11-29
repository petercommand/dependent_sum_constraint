all:
	agda -c --ghc-dont-call-ghc Test/${ARGS}.agda | tee agda-build
	echo "" >> stack-build-tmp
	ghc RemoveChanged.hs && ./RemoveChanged
	./gen_main.sh ${ARGS}
	stack build 2>&1 | tee stack-build-tmp
#	stack build --executable-profiling --library-profiling --ghc-options="-fprof-auto -rtsopts" 2>&1 | tee stack-build-tmp
nix:
	agda -c --ghc-dont-call-ghc --include-path ${AgdaStdlib}/share/agda Test/${ARGS}.agda | tee agda-build
	echo "" >> stack-build-tmp
	./gen_main.sh ${ARGS}
exec:
	stack exec dependent-sum
#	stack exec dependent-sum --profile -- +RTS -p
clean:
	rm -rf MAlonzo/
	stack clean
