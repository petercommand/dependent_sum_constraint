all:
	git submodule init && git submodule update
	cd libsnark/ && git submodule init && git submodule update && mkdir -p build && cd build && env CXXFLAGS="-Wno-unused-variable" cmake .. && make
	$(MAKE) -C agda
	$(MAKE) -C backend_interface
clean:
	$(MAKE) -C agda clean
	rm -rf libsnark/build
exec:
	$(MAKE) -C agda exec
	$(MAKE) -C backend_interface exec
