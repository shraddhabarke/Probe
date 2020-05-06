import csv
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.path as mpath
from collections import defaultdict

columns_euphony = defaultdict(list)
columns = defaultdict(list)
columns_probe = defaultdict(list)
columns_size = defaultdict(list)
columns_cvc4 = defaultdict(list)

with open('euphony-test.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items():
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                columns_euphony[k].append(v)

with open('probe-test.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                columns_probe[k].append(v)

with open('size-test.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader: 
        for (k,v) in row.items(): 
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                columns_size[k].append(v)

with open('cvc4-test.csv') as f:
    reader = csv.DictReader(f) 
    for row in reader:
        for (k,v) in row.items(): 
            if (v != 'Timeout' and v != 'MemoryError' and v != '' and v != None):
                columns_cvc4[k].append(v)

def process_data(col, cols):
    process = list(map(lambda x: float(x), cols[col]))
    process = list(filter(lambda x: x < 600, process))
    process_count = [[x,process.count(x)] for x in set(process)]
    process_count = sorted(process_count, key=lambda x: x[0])
    return process_count

euphony = process_data('Euphony Time (s)',columns_euphony)
size = process_data('Size Based Time (s)',columns_size)
probe = process_data('Probe Time (s)',columns_probe)
cvc4 = process_data('CVC4 Time (s)',columns_cvc4)

star = mpath.Path.unit_regular_star(6)
circle = mpath.Path.unit_circle()
plt.figure(figsize=(15, 7))
plt.xlim(-4,605)
plt.ylim(-4,80) 
plt.plot([x[0] for x in euphony], np.cumsum(np.asarray([x[1] for x in euphony])), 'g^', linewidth=2, label='Euphony', markersize = 4)
plt.legend(loc='best')
plt.plot([x[0] for x in probe], np.cumsum(np.asarray([x[1] for x in probe])), 'o', alpha = 0.7, linewidth=2, label='Probe', markersize = 4)
plt.legend(loc='best')
plt.plot([x[0] for x in size], np.cumsum(np.asarray([x[1] for x in size])), '*', linewidth=2, label='Size', markersize = 4)
plt.legend(loc='best')
plt.plot([x[0] for x in cvc4], np.cumsum(np.asarray([x[1] for x in cvc4])), '+', linewidth=2, label='CVC4', markersize = 4)
plt.legend(loc='best')

plt.xlabel('Time (secs)')
plt.ylabel('# of benchmarks solved')
plt.savefig('cactus-discrete.png')