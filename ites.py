import csv
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.path as mpath
import matplotlib.lines as mlines
import matplotlib.transforms as mtransforms
from collections import defaultdict

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

ite_probe = defaultdict(list)
ite_temp_probe = defaultdict(list)
ite_cvc4 = defaultdict(list)
examples = defaultdict(list)

def line_prepender(filename, line):
    with open(filename, 'r+') as f:
        content = f.read()
        f.seek(0, 0)
        f.write(line.rstrip('\r\n') + '\n' + content)

with open('results/probe.csv', 'r') as f:
    data = f.readlines()
    if data[0] != "Benchmark,Program,Time,Size,Ite\n":
        line_prepender("results/probe.csv", "Benchmark,Program,Time,Size,Ite\n")  

with open('results/cvc4.csv', 'r') as f:
    data = f.readlines()
    if data[0] != "Benchmark,Examples,Program,Time,Ite\n":
        line_prepender("results/cvc4.csv", "Benchmark,Examples,Program,Time,Ite\n") 

with open('results/probe.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                ite_temp_probe[k].append(v)

def process_benchmark(col, cols):
    process = list(map(lambda x: x, cols[col]))
    return process

with open('results/cvc4.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader: 
        for (k,v) in row.items(): 
            if (row['Benchmark'] in process_benchmark('Benchmark', ite_temp_probe) and v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                ite_cvc4[k].append(v)

with open('results/probe.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (row['Benchmark'] in process_benchmark('Benchmark', ite_cvc4) and v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                ite_probe[k].append(v)

def process_ite(col, cols):
    process = list(map(lambda x: x, cols[col]))
    process_int = list(map(lambda x: int(x), process))
    return process_int

cvc4 = process_ite('Ite',ite_cvc4)
probe = process_ite('Ite',ite_probe)
examples = process_ite('Examples',ite_cvc4)
cvc4zip = list(zip(cvc4,examples))
probezip = list(zip(probe,examples))
cvc4ite = list(map(lambda x: x[0]/x[1], cvc4zip))
probeite = list(map(lambda x: x[0]/x[1], probezip))

fig, ax = plt.subplots(figsize=(7, 6))

ax.scatter(cvc4ite, probeite, c='blue', marker='o')
lims = [
    np.min([-0.01, 1]),  # min of both axes
    np.max([0, 1]),  # max of both axes
]
#ax.add_line(line)
ax.plot(lims, lims, 'k-', color='red', alpha=0.75)
ax.set_xlim(lims)
ax.set_ylim(lims)
plt.xlabel('ITEs per example (CVC4)')
plt.ylabel('ITEs per example (Probe)')
plt.savefig('figures/ite.png')