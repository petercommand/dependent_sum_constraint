all:
	git submodule init && git submodule update
	cd libsnark/ && git submodule init && git submodule update && mkdir -p build && cd build && env CXXFLAGS="-Wno-unused-variable" cmake .. && make
	$(MAKE) -C agda
	$(MAKE) -C backend_interface
nix:
	git submodule init && git submodule update
	cd libsnark/ && git submodule init && git submodule update && mkdir -p build && cd build && env CXXFLAGS="-Wno-unused-variable" cmake .. && make
	$(MAKE) nix -C agda
ci:
	git submodule init && git submodule update
	cd libsnark/ && git submodule init && git submodule update && mkdir -p build && cd build && env CXXFLAGS="-Wno-unused-variable" cmake .. && make
	$(MAKE) ci -C agda
	$(MAKE) -C backend_interface
clean:
	$(MAKE) -C agda clean
	rm -rf libsnark/build
ciexec:
	$(MAKE) -C agda ciexec
	$(MAKE) -C backend_interface exec
exec:
	$(MAKE) -C agda exec
	$(MAKE) -C backend_interface exec
