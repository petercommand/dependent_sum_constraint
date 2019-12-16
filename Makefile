all:
	cd libsnark/ && mkdir -p build && cd build && env CXXFLAGS="-Wno-unused-variable" cmake .. && make
	$(MAKE) -C agda
clean:
	$(MAKE) -C agda clean
	rm -rf libsnark/build
exec:
	$(MAKE) -C agda exec
	$(MAKE) -C backend_interface exec
