#!/usr/bin/env python3

import argparse
import logging
from multiprocessing import Pool
import logging.handlers
import os
import subprocess
import time, csv

accuracy_train = [
    "phone-5.sl", "phone-6.sl", "phone-7.sl", "initials.sl", "phone-9.sl", "phone-10.sl", "univ_4.sl",
    "univ_5.sl", "univ_6.sl"
]

accuracy_test = [
    "phone-5-long.sl", "phone-6-long.sl", "phone-7-long.sl", "initials-long.sl", "phone-9-long.sl", 
    "phone-10-long.sl", "univ_4-long.sl", "univ_5-long.sl", "univ_6-long.sl"
]

sanity = ["stackoverflow1.sl", "stackoverflow3.sl", "stackoverflow8.sl", "stackoverflow10.sl", "exceljet1.sl",
            "exceljet2.sl", "initials.sl", "phone-6-long.sl", "43606446.sl", "11604909.sl"]

def run(args):
    times = args.timeout
    if args.cmd == "string":
        files = [i for i in os.listdir("src/test/benchmarks/string/") if i.endswith("sl")]
        if args.strategy == "probe":
            with Pool(1) as pool:
                pool.map(run_probe, files)
        elif args.strategy == "size":
            with Pool(1) as pool:
                pool.map(run_size, files)
        elif args.strategy == "height":
            with Pool(1) as pool:
                pool.map(run_height, files)
    elif args.cmd == "bitvec":
        files = [i for i in os.listdir("src/test/benchmarks/bitvec/") if i.endswith("sl")]
        if args.strategy == "probe":
            with Pool(1) as pool:
                pool.map(run_probe, files)
        elif args.strategy == "size":
            with Pool(1) as pool:
                pool.map(run_size, files)
        elif args.strategy == "height":
            with Pool(1) as pool:
                pool.map(run_height, files)  

def run_size_compare(args):
    if args.cmd == "string":
        files = [i for i in os.listdir("src/test/benchmarks/string/") if i.endswith("sl")]
        if args.strategy == "euphony":
            with Pool(1) as pool:
                pool.map(run_euphony, files)
        elif args.strategy == "cvc4":
            with Pool(1) as pool:
                pool.map(run_cvc4, files)

def run_cvc4(filename):
    with open('results/cvc4.csv') as f:
        reader = csv.reader(f, skipinitialspace=True)
        result = dict((rows[0],rows[2]) for rows in reader)
        key = "string/{}".format(filename)
    try:
        print("src/test/benchmarks/string/{}".format(filename))
        cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/SizeCompute', "src/test/benchmarks/string/{}".format(filename), "{}".format(result[key])]
        output, err  = subprocess.Popen(cmd).communicate()
        print(err)
        output_str = output.decode("utf-8")  
        if (output_str != "" and "memory" not in output_str):
            with open('results/cvc4-size.csv', 'a', newline='') as csvfile:
                csvwriter = csv.writer(csvfile, delimiter=',', quotechar='"', skipinitialspace=True)
                output = map(lambda x: x.rstrip('\n'),output_str.split(','))
                csvwriter.writerow(output)
    except KeyError:
        pass

def run_euphony(filename):
    with open('results/euphony.csv') as f:
        reader = csv.reader(f, skipinitialspace=True)
        result = dict(reader)
    print('Parent process:', os.getppid(), filename)
    print('Process id:', os.getpid())
    key = filename.replace("/home/shraddha/partialcorrectness/src/test/benchmarks/euphony",'')
    try:
        cmd = [ 'java', '-cp','target/scala-2.13/probe-assembly-0.1.jar', 'sygus/SizeCompute', "/home/shraddha/partialcorrectness/src/test/benchmarks/euphony/{}".format(filename), "{}".format(result[key].replace('@',','))]
        output, err  = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
        output_str = output.decode("utf-8")
        if (output_str != "" and "memory" not in output_str):
            with open('results/euphony-size.csv', 'a', newline='') as csvfile:
                csvwriter = csv.writer(csvfile, delimiter=',', quotechar='"', skipinitialspace=True)
                output = map(lambda x: x.rstrip('\n'),output_str.split(','))
                csvwriter.writerow(output)
    except KeyError:
        pass

def run_accuracy(args):
    times = args.timeout
    if args.cmd == "string":
        files = [i for i in os.listdir("src/test/benchmarks/accuracy-expt/") if i.endswith("sl") and i in accuracy_test]
        if args.strategy == "probe":
            with Pool(1) as pool:
                pool.map(run_acc, files)

def run_sanity(args):
    times = args.timeout
    if args.cmd == "string":
        files = [i for i in os.listdir("src/test/benchmarks/string/") if i.endswith("sl") and i in sanity]
        if args.strategy == "probe":
            with Pool(1) as pool:
                pool.map(run_san, files)

def run_acc(filename):
    with open('results/probe-string.csv') as f:
        reader = csv.reader(f, skipinitialspace=True)
        result = dict(reader)
        print(result)
    key = filename.replace('-long','')
    try:
        cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/AccuracyMain', "src/test/benchmarks/accuracy-expt/{}".format(filename), "{}".format(result[key])]
        output, err  = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
        print(err)
        output_str = output.decode("utf-8")
        print(output_str)
        if (output_str != "" and "memory" not in output_str):
            with open('results/probe-accuracy.csv', 'a', newline='') as csvfile:
                csvwriter = csv.writer(csvfile, delimiter=',', quotechar='"', skipinitialspace=True)
                output = map(lambda x: x.rstrip('\n'),output_str.split(','))
                csvwriter.writerow(output)
    except KeyError:
        pass   

def run_size(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/SizeMain', "src/test/benchmarks/string/%s" % (filename) ]
    run_main('results/size.csv', filename, cmd)

def run_height(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/HeightMain', "src/test/benchmarks/string/%s" % (filename) ]
    run_main('results/height.csv', filename, cmd)

def run_main(resultfile, filename, cmd):
    try:
        print("Synthesizing program for %s" % filename)
        run = subprocess.run(cmd,stderr=subprocess.PIPE, stdout=subprocess.PIPE, timeout=times)
        output_str = run.stdout.decode()
        print(output_str)
        if (output_str != "" and "memory" not in output_str):
            with open(resultfile, 'a', newline='') as csvfile:
                csvwriter = csv.writer(csvfile, delimiter=',', quotechar='"')
                output = map(lambda x: x.rstrip('\n'),output_str.split(','))
                csvwriter.writerow(output)
    except MemoryError:
        pass
    except subprocess.TimeoutExpired:   
        pass

def run_probe(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/ProbeMain', "src/test/benchmarks/string/%s" % (filename) ]
    run_main('results/probe.csv', filename, cmd)

def run_san(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/ProbeMain', "src/test/benchmarks/string/%s" % (filename) ]
    run_main('results/sanity.csv', filename, cmd)

def parse_args():
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="cmd")
    subparser = subparsers.add_parser("string", help="Run the String Benchmark Programs")
    subparser.add_argument("--timeout", type = int, default = 600)
    subparser.add_argument("--memory", type = int, default = 16)
    subparser.add_argument("--strategy", type = str, default = "probe")
    subparser.add_argument("--expt", type=str, default="perf")
    subparser = subparsers.add_parser("bitvec", help="Run the BitVector Benchmark Programs")
    subparser.add_argument("--timeout", type = int, default = 600)
    subparser.add_argument("--memory", type = int, default = 16)
    subparser.add_argument("--strategy", type = str, default = "probe")
    return parser.parse_args()

args = parse_args()
times = args.timeout

def main():
    args = parse_args()
    if args.cmd in [ "string", "bitvec"] and args.strategy in [ "probe", "size", "height" ] and args.expt in ["perf"]:
        run(args)
    elif args.cmd in [ "string", "bitvec"] and args.strategy in [ "probe", "size", "height" ] and args.expt in ["accuracy"]:
        run_accuracy(args)
    elif args.cmd in [ "string", "bitvec"] and args.strategy in [ "probe", "size", "height" ] and args.expt in ["sanity"]:
        run_sanity(args)
    elif args.cmd in [ "string", "bitvec"] and args.strategy in [ "euphony", "cvc4" ] and args.expt in ["size-compare"]:
        run_size_compare(args)    
    else:
        print("Invalid Argument")

if __name__ == "__main__":
    if os.path.exists('results/probe.csv') and args.expt in ["perf"] and args.strategy in ["probe"]:
        os.remove('results/probe.csv') 
    elif os.path.exists('results/size.csv') and args.expt in ["perf"] and args.strategy in ["size"]:
        os.remove('results/size.csv') 
    elif os.path.exists('results/height.csv') and args.expt in ["perf"] and args.strategy in ["height"]:
        os.remove('results/height.csv')   
    elif os.path.exists('results/probe-accuracy.csv') and args.expt in ["accuracy"]:
        os.remove('results/probe-accuracy.csv')  
    elif os.path.exists('results/sanity.csv') and args.expt in ["sanity"]:
        os.remove('results/sanity.csv')      
    elif os.path.exists('results/euphony-size.csv') and args.strategy in ["euphony"] and args.expt in ["size-compare"]:
        os.remove('results/euphony-size.csv')    
    elif os.path.exists('results/cvc4-size.csv') and args.strategy in ["cvc4"] and args.expt in ["size-compare"]:
        os.remove('results/cvc4-size.csv')           
    else:
        pass  
    main() 
