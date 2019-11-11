all:
	agda -c --ghc-dont-call-ghc Test/MatrixTest.agda
#	stack build
	stack build --executable-profiling --library-profiling --ghc-options="-fprof-auto -rtsopts"
exec:
	time stack exec dependent-sum --profile -- +RTS -p
clean:
	rm -rf MAlonzo/
	stack clean
