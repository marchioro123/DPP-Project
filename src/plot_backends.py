#!/usr/bin/env python

import matplotlib
matplotlib.use('Agg') # For headless use

import matplotlib.pyplot as plt
import numpy as np
import json
import sys



in_size = len(sys.argv)
data_sizes = list(map(int, sys.argv[-6:]))
title = sys.argv[1]
fig, ax = plt.subplots()

form = ['-', '-.', '--', ':']
col = ['r', 'g', 'b', 'k']
plots = []
labels = []



for i in range(2, in_size-6):

	arg = sys.argv[i]
	arg_lst = arg.split(':')

	progname = arg_lst[0]
	backend = arg_lst[1]
	benchmarks = arg_lst[2].split(',')


	for j in range (0, len(benchmarks)):
		
		benchmark = benchmarks[j]
		benchmark_lst = benchmark.split("_")
		(tree, version) = benchmark_lst

		filename = ('{}-' + backend + '.json').format(progname)
		json_ = json.load(open(filename))

		measurements = json_['{}.fut:{}'.format(progname,benchmark)]['datasets']
		runtimes = list([ np.mean(measurements['data/ps_' + tree + '_{}.in'.format(n)]['runtimes']) / 1000 for n in data_sizes ])
		runtime_plot = ax.plot(data_sizes, runtimes, col[i-2] + form[j], label=(backend + ' ' + tree + ' runtime'))

		plots += runtime_plot



labels += [p.get_label() for p in plots]
ax.set_title(title)
ax.set_xlabel('Input size')
ax.set_ylabel('Runtime (ms)', color='k')
ax.tick_params('y', colors='k')
plt.xticks(data_sizes, rotation='vertical')

ax.legend(plots, labels, loc=0, fontsize = "small")
ax.semilogx()
fig.tight_layout()

plt.rc('text')
plt.savefig('{}.pdf'.format(title), bbox_inches='tight')
