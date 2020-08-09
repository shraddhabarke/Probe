import csv
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.path as mpath
import matplotlib.lines as mlines
import matplotlib.transforms as mtransforms
from collections import defaultdict

def line_prepender(filename, line):
    with open(filename, 'r+') as f:
        content = f.read()
        f.seek(0, 0)
        f.write(line.rstrip('\r\n') + '\n' + content)

with open('results/probe.csv', 'r') as f:
    data = f.readlines()
    if data[0] != "Benchmark,Program,Time,Size,Ite\n":
        line_prepender("results/probe.csv", "Benchmark,Program,Time,Size,Ite\n")  

with open('results/size.csv', 'r') as f:
    data = f.readlines()
    if data[0] != "Benchmark,Program,Time,Sizee\n":
        line_prepender("results/size.csv", "Benchmark,Program,Time,Size\n") 

size_temp_probe = defaultdict(list)
size_size = defaultdict(list)
size_probe = defaultdict(list)
size_euphony = defaultdict(list)

with open('results/probe.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                size_temp_probe[k].append(v)

def process_benchmark(col, cols):
    process = list(map(lambda x: x, cols[col]))
    return process

with open('results/size.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader: 
        for (k,v) in row.items(): 
            if (row['Benchmark'] in process_benchmark('Benchmark', size_temp_probe) and v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                size_size[k].append(v)

with open('results/probe.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (row['Benchmark'] in process_benchmark('Benchmark', size_size) and v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                size_probe[k].append(v)

def process_data(col, cols):
    process = list(map(lambda x: int(x), cols[col]))
    process_count = [[x,process.count(x)] for x in set(process)]
    process_count = sorted(process_count, key=lambda x: x[0])
    return process_count

def process_size(col, cols):
    process = list(map(lambda x: x, cols[col]))
    process_int = list(map(lambda x: int(x), process))
    print(process_int)
    return process_int

size = process_size('Size',size_size)
probe = process_size('Size',size_probe)

probebench = process_benchmark('Benchmark',size_probe)
sizebench = process_benchmark('Benchmark',size_size)

fig, ax = plt.subplots(figsize=(7, 6))

ax.scatter(probe, size, c='red', marker='*')
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

plt.xlabel('Number of AST nodes in program (Probe)')
plt.ylabel('Number of AST nodes in program (Size-Based)')

#plt.savefig('/home/shraddha/oopsla-2020/figures/size-graph.png')

plt.savefig('figures/size-graph-size.png')
