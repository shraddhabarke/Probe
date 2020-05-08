import subprocess, csv, multiprocessing
from multiprocessing import Pool
import os
import functools
from os import getpid

files = [i for i in os.listdir("/home/shraddha/partialcorrectness/src/test/benchmarks/quality-tests") if i.endswith("sl")]

def run_cvc4(filename):
    with open('cvc4-string.csv') as f:
        reader = csv.reader(f, skipinitialspace=True)
        result = dict(reader)
    print('Parent process:', os.getppid(), filename)
    print('Process id:', os.getpid())
    key = filename.replace('-long','')
    cmd = [ 'java', '-cp','target/scala-2.13/probe-assembly-0.1.jar', 'sygus/AccuracyMain', "/home/shraddha/partialcorrectness/src/test/benchmarks/quality-tests/{}".format(filename), "{}".format(result[key].replace('@',','))]
    #try:
    output, err  = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
    print(err)
    output_str = output.decode("utf-8")
    print(output_str)
    if (output_str != "" and "memory" not in output_str):
        with open('cvc4-accuracy.csv', 'a', newline='') as csvfile:
            csvwriter = csv.writer(csvfile, quotechar='"',quoting=csv.QUOTE_ALL, delimiter=',',skipinitialspace=True)
            output = map(lambda x: x.rstrip('\n'),output_str.split(','))
            csvwriter.writerow(output)
    #except MemoryError:
     #   pass
    #except subprocess.TimeoutExpired:   
     #   pass

def run_probe(filename):
    with open('probe-string.csv') as f:
        reader = csv.reader(f, skipinitialspace=True)
        result = dict(reader)
    print('Parent process:', os.getppid(), filename)
    print('Process id:', os.getpid())
    key = filename.replace('-long','')
    try:
        cmd = [ 'java', '-cp','target/scala-2.13/probe-assembly-0.1.jar', 'sygus/AccuracyMain', "/home/shraddha/partialcorrectness/src/test/benchmarks/quality-tests/{}".format(filename), "{}".format(result[key].replace('@',','))]
        output, err  = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
        print(err)
        output_str = output.decode("utf-8")
        print(output_str)
        if (output_str != "" and "memory" not in output_str):
            with open('probe-accuracy.csv', 'a', newline='') as csvfile:
                csvwriter = csv.writer(csvfile, quotechar='"',quoting=csv.QUOTE_ALL, delimiter=',',skipinitialspace=True)
                output = map(lambda x: x.rstrip('\n'),output_str.split(','))
                csvwriter.writerow(output)
    except KeyError:
        pass
    #except subprocess.TimeoutExpired:   
     #   pass   

def run_euphony(filename):
    with open('euphony-string.csv') as f:
        reader = csv.reader(f, skipinitialspace=True)
        result = dict(reader)
    print('Parent process:', os.getppid(), filename)
    print('Process id:', os.getpid())
    key = filename.replace('-long','')
    try:
        cmd = [ 'java', '-cp','target/scala-2.13/probe-assembly-0.1.jar', 'sygus/AccuracyMain', "/home/shraddha/partialcorrectness/src/test/benchmarks/quality-tests/{}".format(filename), "{}".format(result[key].replace('@',','))]
        output, err  = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
        print(err)
        output_str = output.decode("utf-8")
        print(output_str)
        if (output_str != "" and "memory" not in output_str):
            with open('euphony-accuracy.csv', 'a', newline='') as csvfile:
                csvwriter = csv.writer(csvfile, quotechar='"',quoting=csv.QUOTE_ALL, delimiter=',',skipinitialspace=True)
                output = map(lambda x: x.rstrip('\n'),output_str.split(','))
                csvwriter.writerow(output)
    except KeyError:
        pass
    #except subprocess.TimeoutExpired:   
     #   pass    

if __name__ == '__main__':
    #with Pool(1) as pool:
     #   pool.map(run_cvc4, files)
    #with Pool(1) as pool:
     #   pool.map(run_probe, files)
    with Pool(1) as pool:
        pool.map(run_euphony, files)  