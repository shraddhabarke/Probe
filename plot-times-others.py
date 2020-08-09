import csv
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.path as mpath
from collections import defaultdict
import statistics as stat

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

time_probe = defaultdict(list)
time_euphony = defaultdict(list)
time_cvc4 = defaultdict(list)

with open('results/probe.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                time_probe[k].append(v)

with open('results/euphony.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                time_euphony[k].append(v)

with open('results/cvc4.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                time_cvc4[k].append(v)

def process_data(col, cols):
    process = list(map(lambda x: float(x), cols[col]))
    process_valid = list(filter(lambda x: x < 600, process))
    process_count = [[x,process.count(x)] for x in set(process_valid)]
    process_count = sorted(process_count, key=lambda x: x[0])
    return process_count

euphony = process_data('Time',time_euphony)
probe = process_data('Time',time_probe)
cvc4 = process_data('Time',time_cvc4)

cvc4.append([600,0])
probe.append([600,0])
euphony.append([600,0])

plt.figure(figsize=(15, 7))
plt.xlim(-4,605)
plt.ylim(-4,83) 
plt.plot([x[0] for x in cvc4], np.cumsum(np.asarray([x[1] for x in cvc4])), 'r--', linewidth=2, label='CVC4', markersize = 4)
plt.legend(loc='best')
plt.plot([x[0] for x in euphony], np.cumsum(np.asarray([x[1] for x in euphony])), 'g--', linewidth=2, label='Euphony', markersize = 4)
plt.legend(loc='best')
plt.plot([x[0] for x in probe], np.cumsum(np.asarray([x[1] for x in probe])), 'b--', linewidth=2, label='Probe', markersize = 4)
plt.legend(loc='best')

plt.xlabel('Time (seconds)')
plt.ylabel('Number of benchmarks solved')
plt.savefig('figures/probe-vs-others.png')
