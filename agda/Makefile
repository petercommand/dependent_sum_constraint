all:
	agda -c --ghc-dont-call-ghc Test/${ARGS}.agda | tee agda-build
	echo ${PWD} > agda_dir
	ghc RemoveChanged.hs && ./RemoveChanged
	./gen_main.sh ${ARGS}
	stack build &> stack-build-tmp
#	stack build --executable-profiling --library-profiling --ghc-options="-fprof-auto -rtsopts" 2>&1 | tee stack-build-tmp
exec:
	stack exec dependent-sum
#	stack exec dependent-sum --profile -- +RTS -p
clean:
	rm -rf MAlonzo/
	stack clean
