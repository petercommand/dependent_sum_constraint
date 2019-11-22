all:
	agda -c --ghc-dont-call-ghc Test/${ARGS}.agda
	./gen_main.sh ${ARGS}
	stack build
#	stack build --executable-profiling --library-profiling --ghc-options="-fprof-auto -rtsopts"
exec:
	stack exec dependent-sum > out
#	time stack exec dependent-sum --profile -- +RTS -p
clean:
	rm -rf MAlonzo/
	stack clean
