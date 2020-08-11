all:
	rm -rf dependent-vc
	agda -c --ghc-dont-call-ghc --include-path ${AgdaStdlib}/share/agda Test/${ARGS}.agda
	ghc -O -i$./ -Werror ./MAlonzo/Code/Test/${ARGS}.hs -main-is MAlonzo.Code.Test.${ARGS} --make -fwarn-incomplete-patterns -fno-warn-overlapping-patterns -o dependent-vc
exec:
	rm -rf constraints constraints_serialize inputvars outvars solve.result
	./dependent-vc
clean:
	rm -rf MAlonzo/
	rm -rf dependent-vc
