all:
	agda -c --ghc-dont-call-ghc --include-path ${AgdaStdlib}/share/agda Test/${ARGS}.agda | tee agda-build
	echo "" >> stack-build-tmp
	ghc -O -i$./ -Werror ./MAlonzo/Code/Test/${ARGS}.hs -main-is MAlonzo.Code.Test.${ARGS} --make -fwarn-incomplete-patterns -fno-warn-overlapping-patterns -o dependent-vc
exec:
	./dependent-vc
clean:
	rm -rf MAlonzo/
	rm -rf dependent-vc
