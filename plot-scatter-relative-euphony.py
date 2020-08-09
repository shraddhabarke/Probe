import csv
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.path as mpath
import matplotlib.lines as mlines
import matplotlib.transforms as mtransforms
from collections import defaultdict

size_temp_probe = defaultdict(list)
size_probe = defaultdict(list)
size_euphony = defaultdict(list)

def postprocess(filename):
    with open(filename, 'r') as file :
      filedata = file.read()
    filedata = filedata.replace('""","""', '"",""')
    with open(filename, 'w') as file:
      file.write(filedata)

postprocess('results/probe.csv')

with open('results/probe.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                size_temp_probe[k].append(v)

def process_benchmark(col, cols):
    process = list(map(lambda x: x, cols[col]))
    return process

with open('results/euphony-size.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader: 
        for (k,v) in row.items(): 
            if (row['Benchmark'] in process_benchmark('Benchmark', size_temp_probe) and v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                size_euphony[k].append(v)

with open('results/probe.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (row['Benchmark'] in process_benchmark('Benchmark', size_euphony) and v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                size_probe[k].append(v)

def process_data(col, cols):
    process = list(map(lambda x: int(x), cols[col]))
    process_count = [[x,process.count(x)] for x in set(process)]
    process_count = sorted(process_count, key=lambda x: x[0])
    return process_count

def process_size(col, cols):
    process = list(map(lambda x: x, cols[col]))
    process_int = list(map(lambda x: int(x), process))
    return process_int

#euphony = process_size('Size',size_euphony)
euphony = process_size('Size',size_euphony)
probe = process_size('Size',size_probe)
print(list(zip(probe,euphony)))
zip = [x for x in euphony if x < probe[euphony.index(x)]]

probebench = process_benchmark('Benchmark',size_probe)
sizebench = process_benchmark('Benchmark',size_euphony)

#plt.plot([x[0] for x in euphony], [x[1] for x in euphony],  'r^', linewidth=2, label='Euphony', markersize = 4)
#plt.legend(loc='best')

fig, ax = plt.subplots(figsize=(7, 6))

#line = mlines.Line2D([0, 1], [0, 1], color='red')
#transform = ax.transAxes
#line.set_transform(transform)

ax.scatter(probe, euphony, c='red', marker='*')
lims = [
    np.min([1, 1]),  # min of both axes
    np.max([1000, 1000]),  # max of both axes
]
#ax.add_line(line)
ax.plot(lims, lims, 'k-', color='red', alpha=0.75, zorder=0)

ax.set_xlim(lims)
ax.set_ylim(lims)
plt.xscale('log')
plt.yscale('log')
plt.ylim(1,1000)
plt.xlim(1,1000)


#plt.plot(probe, cvc4, 'r^', alpha = 0.7, linewidth=2, label='Probe', markersize = 4)
#plt.legend(loc='best')
#plt.plot(cvc4, '+', linewidth=2, label='CVC4', markersize = 4)
#plt.legend(loc='best')
#print(len(cvc4), len(probe))
#g^
#o
#'+'
plt.xlabel('Number of AST nodes in program (Probe)')
plt.ylabel('Number of AST nodes in program (Euphony)')

#plt.savefig('/home/shraddha/oopsla-2020/figures/size-graph.png')

plt.savefig('figures/size-graph-euphony.png')
