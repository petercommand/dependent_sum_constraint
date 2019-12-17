all:
	agda -c --ghc-dont-call-ghc --include-path ${AgdaStdlib}/share/agda Test/${ARGS}.agda | tee agda-build
	echo "" >> stack-build-tmp
#	ghc RemoveChanged.hs && ./RemoveChanged
	./gen_main.sh ${ARGS}
	ghc -O -i$./ -Werror ./MAlonzo/Code/Test/${ARGS}.hs -main-is MAlonzo.Code.Test.${ARGS} --make -fwarn-incomplete-patterns -fno-warn-overlapping-patterns -o dependent-sum
#	stack build 2>&1 | tee stack-build-tmp
#	stack build --executable-profiling --library-profiling --ghc-options="-fprof-auto -rtsopts" 2>&1 | tee stack-build-tmp
nix:
	agda -c --ghc-dont-call-ghc --include-path ${AgdaStdlib}/share/agda Test/${ARGS}.agda | tee agda-build
	echo "" >> stack-build-tmp
	./gen_main.sh ${ARGS}
ci:
	agda -c --ghc-dont-call-ghc --include-path ${AgdaStdlib}/share/agda Test/${ARGS}.agda | tee agda-build
	echo "" >> stack-build-tmp
	./gen_main.sh ${ARGS}
	ghc -O -i$./ -Werror ./MAlonzo/Code/Test/${ARGS}.hs -main-is MAlonzo.Code.Test.${ARGS} --make -fwarn-incomplete-patterns -fno-warn-overlapping-patterns -o dependent-sum
ciexec:
	./dependent-sum
exec:
	./dependent-sum
#	stack exec dependent-sum
#	stack exec dependent-sum --profile -- +RTS -p
clean:
	rm -rf MAlonzo/
	stack clean
