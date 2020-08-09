import csv
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.path as mpath
import matplotlib.lines as mlines
import matplotlib.transforms as mtransforms
from collections import defaultdict

size_temp_probe = defaultdict(list)
size_cvc4 = defaultdict(list)
size_probe = defaultdict(list)

def postprocess(filename):
    with open(filename, 'r') as file :
      filedata = file.read()
    filedata = filedata.replace('""","""', '"",""')
    with open(filename, 'w') as file:
      file.write(filedata)

def postprocess_cvc4(filename):
    with open(filename, 'r') as file :
      filedata = file.read()
    filedata = filedata.replace('","', '"@"')
    with open(filename, 'w') as file:
      file.write(filedata)

postprocess('results/probe.csv')
postprocess_cvc4('results/cvc4.csv')

with open('results/probe.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                size_temp_probe[k].append(v)

def process_benchmark(col, cols):
    process = list(map(lambda x: x, cols[col]))
    return process

with open('results/cvc4-size.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader: 
        for (k,v) in row.items(): 
            if (row['Benchmark'] in process_benchmark('Benchmark', size_temp_probe) and v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                size_cvc4[k].append(v)

def line_prepender(filename, line):
    with open(filename, 'r+') as f:
        content = f.read()
        f.seek(0, 0)
        f.write(line.rstrip('\r\n') + '\n' + content)

with open('results/probe.csv', 'r') as f:
    data = f.readlines()
    if data[0] != "Benchmark,Program,Time,Size,Ite\n":
        line_prepender("results/probe.csv", "Benchmark,Program,Time,Size,Ite\n")  

with open('results/probe.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (row['Benchmark'] in process_benchmark('Benchmark', size_cvc4) and v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
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

cvc4 = process_size('Size',size_cvc4)
probe = process_size('Size',size_probe)
print(sum(cvc4)/len(cvc4))
print(sum(probe)/len(probe))

probebench = process_benchmark('Benchmark',size_probe)
sizebench = process_benchmark('Benchmark',size_cvc4)

print(probebench[-14], probe[-14], cvc4[-14])

fig, ax = plt.subplots(figsize=(7, 6))

ax.scatter(probe, cvc4, c='black', marker='*')
lims = [
    np.min([1, 1]),  # min of both axes
    np.max([1000, 1000]),  # max of both axes
]

ax.plot(lims, lims, 'k-', color='red', alpha=0.75, zorder=0)

ax.set_xlim(lims)
ax.set_ylim(lims)
plt.xscale('log')
plt.yscale('log')
plt.ylim(1,1000)
plt.xlim(1,1000)

plt.xlabel('Number of AST nodes in program (Probe)')
plt.ylabel('Number of AST nodes in program (CVC4)')


plt.savefig('figures/size-graph-cvc4.png')
