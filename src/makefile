
.PHONY: clean benchmark test plot all


# General commands
all: test benchmark plot

clean:
	rm -fr data lib futhark.pkg *.actual *.expected \
	tests helpers *.c *.json *.pdf


# Analysis
test: lib tests.fut
	printf "\n\n--------------------------------------------\n\
----------- TESTING SEQUENTIAL -------------\n\
--------------------------------------------\n\n"
	futhark test --backend=c tests.fut
	printf "\n\n--------------------------------------------\n\
----------- TESTING PARALLEL ---------------\n\
--------------------------------------------\n\n"
	futhark test --backend=cuda tests.fut

benchmark: data
	printf "\n\n--------------------------------------------\n\
----------- BENCHMARKS C BACKEND -----------\n\
--------------------------------------------\n\n"
	futhark bench --backend=c --json tests-c.json tests.fut
	printf "\n\n--------------------------------------------\n\
----------- BENCHMARKS CUDA BACKEND --------\n\
--------------------------------------------\n\n"
	futhark bench --backend=cuda --json tests-cuda.json tests.fut
	printf "\n\n--------------------------------------------\n\
----------- BENCHMARKS OPENCL BACKEND ------\n\
--------------------------------------------\n\n"
	futhark bench --backend=opencl --json tests-opencl.json tests.fut


# Benchmark plotting
plot: conv_naive.pdf conv_improved.pdf conv_comparison.pdf \
	  naive_parallel.pdf improved_parallel.pdf

conv_comparison.pdf: plot.py tests-c.json tests-cuda.json
	python3 plot.py conv_comparison tests:cuda:flat_naive,chain_naive,binary_naive \
							   	    tests:cuda:flat_improved,chain_improved,binary_improved \
							   		$(SIZES)

conv_naive.pdf: plot.py tests-c.json tests-cuda.json
	python3 plot.py conv_naive tests:c:flat_naive,chain_naive,binary_naive \
							   tests:cuda:flat_naive,chain_naive,binary_naive \
							   $(SIZES)

conv_improved.pdf: plot.py tests-c.json tests-cuda.json
	python3 plot.py conv_improved tests:c:flat_improved,chain_improved,binary_improved,random_improved \
							 	  tests:cuda:flat_improved,chain_improved,binary_improved,random_improved \
							 	  $(SIZES)


naive_parallel.pdf: plot.py tests-c.json tests-cuda.json tests-opencl.json
	python3 plot.py naive_parallel tests:cuda:flat_naive,chain_naive,binary_naive \
							       tests:opencl:flat_naive,chain_naive,binary_naive \
							       $(SIZES)

improved_parallel.pdf: plot.py tests-c.json tests-cuda.json tests-opencl.json
	python3 plot.py improved_parallel tests:cuda:flat_improved,chain_improved,binary_improved,random_improved \
							 	      tests:opencl:flat_improved,chain_improved,binary_improved,random_improved \
							 	      $(SIZES)


# Data generation
data: data/.generated

data/.generated: helpers
	mkdir -p data
	for SIZE in $(SIZES); do \
		echo $$SIZE | ./helpers -e make_flat_parents > data/ps_flat_$$SIZE.in; \
		echo $$SIZE | ./helpers -e make_chain_parents > data/ps_chain_$$SIZE.in; \
		echo $$SIZE | ./helpers -e make_binary_parents > data/ps_binary_$$SIZE.in; \
		echo "0 $$SIZE" | ./helpers -e random_parent_vector > data/ps_random_$$SIZE.in; \
	done
	touch $@


# Benchmark .json compilation
tests-c.json: data tests.fut parents_conv.fut directed_conv.fut undirected_conv.fut
	futhark bench --backend=c --json tests-c.json tests.fut

tests-cuda.json: data tests.fut parents_conv.fut directed_conv.fut undirected_conv.fut
	futhark bench --backend=cuda --json tests-cuda.json tests.fut

tests-opencl.json: data tests.fut parents_conv.fut directed_conv.fut undirected_conv.fut
	futhark bench --backend=opencl --json tests-opencl.json tests.fut


# Library/utility compilation
helpers: lib helpers.fut
	futhark c helpers.fut

lib:
	futhark pkg add github.com/diku-dk/sorts
	futhark pkg add github.com/diku-dk/cpprandom
	futhark pkg sync

SIZES = 100 1000 10000 100000 1000000 10000000
