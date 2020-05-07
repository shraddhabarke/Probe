import subprocess, csv, multiprocessing
from multiprocessing import Pool
import os
import functools
from os import getpid

files = [i for i in os.listdir("/home/shraddha/partialcorrectness/src/test/benchmarks/euphony") if i.endswith("sl")]

def run_probe(filename):
    print('Parent process:', os.getppid(), filename)
    print('Process id:', os.getpid())
    cmd = [ 'java', '-cp','target/scala-2.13/probe-assembly-0.1.jar', 'sygus/ProbeMain', "/home/shraddha/partialcorrectness/src/test/benchmarks/euphony/%s" % (filename) ]
    try:
        run = subprocess.run(cmd,stderr=subprocess.PIPE, stdout=subprocess.PIPE, timeout=600)
        output_str = run.stdout.decode('utf-8')
        if (output_str != "" and "memory" not in output_str):
            with open('probe.csv', 'a', newline='') as csvfile:
                csvwriter = csv.writer(csvfile, quoting=csv.QUOTE_ALL)
                output = map(lambda x: x.rstrip('\n'),output_str.split(','))
                csvwriter.writerow(output)
    except MemoryError:
        pass
    except subprocess.TimeoutExpired:   
        pass

def run_size(filename):
    print('Parent process:', os.getppid(), filename)
    print('Process id:', os.getpid())
    cmd = [ 'java', '-cp','target/scala-2.13/probe-assembly-0.1.jar', 'sygus/SizeMain', "/home/shraddha/partialcorrectness/src/test/benchmarks/euphony/%s" % (filename) ]
    try:
        run = subprocess.run(cmd,stderr=subprocess.PIPE, stdout=subprocess.PIPE, timeout=600)
        output_str = run.stdout.decode('utf-8')
        if (output_str != "" and "memory" not in output_str):
            with open('size.csv', 'a', newline='') as csvfile:
                csvwriter = csv.writer(csvfile, quoting=csv.QUOTE_ALL)
                output = map(lambda x: x.rstrip('\n'),output_str.split(','))
                csvwriter.writerow(output)
    except MemoryError:
        pass
    except subprocess.TimeoutExpired:   
        pass

def run_height(filename):
    print('Parent process:', os.getppid(), filename)
    print('Process id:', os.getpid())
    cmd = [ 'java', '-cp','target/scala-2.13/probe-assembly-0.1.jar', 'sygus/HeightMain', "/home/shraddha/partialcorrectness/src/test/benchmarks/euphony/%s" % (filename) ]
    try:
        run = subprocess.run(cmd,stderr=subprocess.PIPE, stdout=subprocess.PIPE, timeout=600)
        output_str = run.stdout.decode('utf-8')
        if (output_str != "" and "memory" not in output_str):
            with open('height.csv', 'a', newline='') as csvfile:
                csvwriter = csv.writer(csvfile, quoting=csv.QUOTE_ALL)
                output = map(lambda x: x.rstrip('\n'),output_str.split(','))
                csvwriter.writerow(output)
    except MemoryError:
        pass
    except subprocess.TimeoutExpired:   
        pass

if __name__ == '__main__':
    with Pool(2) as pool:
        pool.map(run_height, files)
    
    with Pool(2) as pool:
        pool.map(run_probe, files)


       
