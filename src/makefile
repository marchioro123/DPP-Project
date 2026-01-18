
.PHONY: clean benchmark test plot all


# General commands
all: test plot

clean:
	rm -fr data lib futhark.pkg *.actual *.expected \
	tests helpers *.c *.json *.pdf


# Analysis
test: data lib tests.fut
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
	futhark bench --backend=c tests.fut
	printf "\n\n--------------------------------------------\n\
----------- BENCHMARKS CUDA BACKEND --------\n\
--------------------------------------------\n\n"
	futhark bench --backend=cuda tests.fut
	printf "\n\n--------------------------------------------\n\
----------- BENCHMARKS OPENCL BACKEND ------\n\
--------------------------------------------\n\n"
	futhark bench --backend=opencl tests.fut


# Benchmark plotting
plot: conv_constrained.pdf conv_general.pdf \
	  conv_sequential_comparison.pdf conv_parallel_comparison.pdf \
	  conv_constrained_parallel.pdf conv_general_parallel.pdf

conv_constrained.pdf: plot.py tests-c.json tests-cuda.json
	python3 plot.py conv_constrained tests:c:flat_constrained,chain_constrained,binary_constrained \
							   		 tests:cuda:flat_constrained,chain_constrained,binary_constrained \
							   		 $(SIZES)

conv_general.pdf: plot.py tests-c.json tests-cuda.json
	python3 plot.py conv_general tests:c:flat_general,chain_general,binary_general,random_general \
							 	 tests:cuda:flat_general,chain_general,binary_general,random_general \
							 	 $(SIZES)

conv_sequential_comparison.pdf: plot.py tests-c.json
	python3 plot.py conv_sequential_comparison tests:c:flat_constrained,chain_constrained,binary_constrained \
							   	    		   tests:c:flat_general,chain_general,binary_general \
							   				   $(SIZES)

conv_parallel_comparison.pdf: plot.py tests-cuda.json
	python3 plot.py conv_parallel_comparison tests:cuda:flat_constrained,chain_constrained,binary_constrained \
							   	    		 tests:cuda:flat_general,chain_general,binary_general \
							   				 $(SIZES)


conv_constrained_parallel.pdf: plot.py tests-cuda.json tests-opencl.json
	python3 plot.py conv_constrained_parallel tests:cuda:flat_constrained,chain_constrained,binary_constrained \
							       			  tests:opencl:flat_constrained,chain_constrained,binary_constrained \
							       			  $(SIZES)

conv_general_parallel.pdf: plot.py tests-cuda.json tests-opencl.json
	python3 plot.py conv_general_parallel tests:cuda:flat_general,chain_general,binary_general,random_general \
							 	          tests:opencl:flat_general,chain_general,binary_general,random_general \
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
