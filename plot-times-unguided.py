import csv
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.path as mpath
from collections import defaultdict

def postprocess(filename):
    with open(filename, 'r') as file :
      filedata = file.read()
    filedata = filedata.replace('""","""', '"",""')
    with open(filename, 'w') as file:
      file.write(filedata)

def line_prepender(filename, line):
    with open(filename, 'r+') as f:
        content = f.read()
        f.seek(0, 0)
        f.write(line.rstrip('\r\n') + '\n' + content)

postprocess('results/probe.csv')
postprocess('results/size.csv')
postprocess('results/height.csv')

with open('results/probe.csv', 'r') as f:
    data = f.readlines()
    print(data[0])
    if data[0] != "Benchmark,Program,Time,Size,Ite\n":
        line_prepender("results/probe.csv", "Benchmark,Program,Time,Size,Ite\n")       

with open('results/size.csv', 'r') as f:
    data = f.readlines()
    print(data[0])
    if data[0] != "Benchmark,Program,Time,Size\n":
        line_prepender("results/size.csv", "Benchmark,Program,Time,Size\n")

with open('results/height.csv', 'r') as f:
    data = f.readlines()
    print(data[0])
    if data[0] != "Benchmark,Program,Time,Size\n":
        line_prepender("results/height.csv", "Benchmark,Program,Time,Size\n")

time_height = defaultdict(list)
time_probe = defaultdict(list)
time_size = defaultdict(list)

with open('results/size.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader: 
        for (k,v) in row.items(): 
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                time_size[k].append(v)

with open('results/height.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                time_height[k].append(v)

with open('results/probe.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                time_probe[k].append(v)


def process_data(col, cols):
    process = list(map(lambda x: float(x), cols[col]))
    process_count = [[x,process.count(x)] for x in set(process)]
    process_count = sorted(process_count, key=lambda x: x[0])
    return process_count

size = process_data('Time',time_size)
height = process_data('Time',time_height)
probe = process_data('Time',time_probe)


print(list(zip([x[0] for x in probe], np.cumsum(np.asarray([x[1] for x in probe])))))
print(list(zip([x[0] for x in size], np.cumsum(np.asarray([x[1] for x in size])))))
print(list(zip([x[0] for x in height], np.cumsum(np.asarray([x[1] for x in height])))))

size.append([600,0])
height.append([600,0])
probe.append([600,0])

plt.figure(figsize=(15, 7))
plt.xlim(-4,605)
plt.ylim(-4,80) 
plt.plot([x[0] for x in probe], np.cumsum(np.asarray([x[1] for x in probe])), 'b--', linewidth=2, label='Probe', markersize = 4)
plt.legend(loc='best')
plt.plot([x[0] for x in size], np.cumsum(np.asarray([x[1] for x in size])), 'g--', linewidth=2, label='Size-based', markersize = 4)
plt.legend(loc='best')
plt.plot([x[0] for x in height], np.cumsum(np.asarray([x[1] for x in height])), 'r--', linewidth=2, label='Height-based', markersize = 4)
plt.legend(loc='best')

plt.xlabel('Time (seconds)')
plt.ylabel('Number of benchmarks solved')
plt.savefig('figures/probe-vs-unguided.png')
