#!/usr/bin/env python3

import argparse
import logging
from multiprocessing import Pool
import logging.handlers
import os
import subprocess
import time, csv

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
        files = [i for i in os.listdir("src/test/benchmarks/hackers-delight/") if i.endswith("sl")]
        if args.strategy == "probe":
            with Pool(1) as pool:
                pool.map(run_probe_bitvec, files)
        elif args.strategy == "size":
            with Pool(1) as pool:
                pool.map(run_size_bitvec, files)
        elif args.strategy == "height":
            with Pool(1) as pool:
                pool.map(run_height_bitvec, files) 
    elif args.cmd == "circuit":
        files = [i for i in os.listdir("src/test/benchmarks/circuit/test/") if i.endswith("sl")]
        if args.strategy == "probe":
            with Pool(1) as pool:
                pool.map(run_probe_circuit, files)
        elif args.strategy == "size":
            with Pool(1) as pool:
                pool.map(run_size_circuit, files)
        elif args.strategy == "height":
            with Pool(1) as pool:
                pool.map(run_height_circuit, files)             

def run_larger(args):
    times = args.timeout
    if args.cmd == "string":
        files = [i for i in os.listdir("src/test/benchmarks/larger-grammar/") if i.endswith("sl")]
        if args.strategy == "probe":
            with Pool(1) as pool:
                pool.map(run_probe_larger, files)
        elif args.strategy == "size":
            with Pool(1) as pool:
                pool.map(run_size_larger, files)
        elif args.strategy == "height":
            with Pool(1) as pool:
                pool.map(run_height_larger, files)        

def run_accuracy(args):
    times = args.timeout
    if args.cmd == "string":
        files = [i for i in os.listdir("src/test/benchmarks/accuracy-expt/") if i.endswith("sl") and i in accuracy_test]
        if args.strategy == "probe":
            with Pool(1) as pool:
                pool.map(run_acc_probe, files)
        elif args.strategy == "cvc4":
            with Pool(1) as pool:
                pool.map(run_acc_cvc, files)        

def run_sanity(args):
    times = args.timeout
    if args.cmd == "string":
        files = [i for i in os.listdir("src/test/benchmarks/string/") if i.endswith("sl") and i in sanity]
        if args.strategy == "probe":
            with Pool(1) as pool:
                pool.map(run_san, files)

def run_acc_probe(filename):
    with open('results/probe-train.csv') as f:
        reader = csv.reader(f, skipinitialspace=True)
        result = dict(reader)
    key = filename.replace('-long','')
    try:
        cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/AccuracyMain', "src/test/benchmarks/accuracy-expt/{}".format(filename), "{}".format(result[key])]
        output, err  = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
        output_str = output.decode("utf-8")
        print(output_str)
        if (output_str != "" and "memory" not in output_str):
            with open('results/probe-accuracy.csv', 'a', newline='') as csvfile:
                csvwriter = csv.writer(csvfile, delimiter=',', quotechar='"', skipinitialspace=True)
                output = map(lambda x: x.rstrip('\n'),output_str.split(','))
                csvwriter.writerow(output)
    except KeyError:
        pass

def run_acc_cvc(filename):
    with open('results/cvc4-train.csv') as f:
        reader = csv.reader(f, skipinitialspace=True)
        result = dict(reader)
    key = filename.replace('-long','')
    try:
        cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/AccuracyMain', "src/test/benchmarks/accuracy-expt/{}".format(filename), "{}".format(result[key])]
        output, err  = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
        output_str = output.decode("utf-8")
        print(output_str)
        if (output_str != "" and "memory" not in output_str):
            with open('results/cvc4-accuracy.csv', 'a', newline='') as csvfile:
                csvwriter = csv.writer(csvfile, delimiter=',', quotechar='"', skipinitialspace=True)
                output = map(lambda x: x.rstrip('\n'),output_str.split(','))
                csvwriter.writerow(output)
    except KeyError:
        pass   

def run_size(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/SizeMain', "src/test/benchmarks/string/%s" % (filename) ]
    run_main('results/size.csv', filename, cmd)

def run_size_bitvec(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/SizeMain', "src/test/benchmarks/hackers-delight/%s" % (filename) ]
    run_main('results/size-bitvec.csv', filename, cmd)

def run_size_circuit(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/SizeMain', "src/test/benchmarks/circuit/test/%s" % (filename) ]
    run_main('results/size-circuit.csv', filename, cmd)

def run_size_larger(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/SizeMain', "src/test/benchmarks/larger-grammar/%s" % (filename) ]
    run_main('results/size-larger.csv', filename, cmd)

def run_height_larger(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/HeightMain', "src/test/benchmarks/larger-grammar/%s" % (filename) ]
    run_main('results/height-larger.csv', filename, cmd)

def run_height(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/HeightMain', "src/test/benchmarks/string/%s" % (filename) ]
    run_main('results/height.csv', filename, cmd)

def run_height_bitvec(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/HeightMain', "src/test/benchmarks/hackers-delight/%s" % (filename) ]
    run_main('results/height-bitvec.csv', filename, cmd)

def run_height_circuit(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/HeightMain', "src/test/benchmarks/circuit/test/%s" % (filename) ]
    run_main('results/height-circuit.csv', filename, cmd)

def run_main(resultfile, filename, cmd):
    try:
        print("Synthesizing program for %s" % filename)
        run = subprocess.run(cmd,stderr=subprocess.PIPE, stdout=subprocess.PIPE, timeout=times)
        output_str = run.stdout.decode()
        print(output_str)
        if (output_str != "" and "memory" not in output_str):
            with open(resultfile, 'a', newline='') as csvfile:
                csvwriter = csv.writer(csvfile, delimiter=',', quoting=csv.QUOTE_MINIMAL)
                output = map(lambda x: x.rstrip('\n'),output_str.split(','))
                csvwriter.writerow(output)
    except MemoryError:
        pass
    except subprocess.TimeoutExpired:   
        pass

def run_probe(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/ProbeMain', "src/test/benchmarks/string/%s" % (filename) ]
    run_main('results/probe.csv', filename, cmd)

def run_probe_bitvec(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/ProbeMain', "src/test/benchmarks/hackers-delight/%s" % (filename) ]
    run_main('results/probe-bitvec.csv', filename, cmd)

def run_probe_circuit(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/ProbeMain', "src/test/benchmarks/circuit/test/%s" % (filename) ]
    run_main('results/probe-circuit.csv', filename, cmd)

def run_probe_larger(filename):
    cmd = [ 'java', '-cp','target/scala-2.12/probe-assembly-0.1.jar', 'sygus/ProbeMain', "src/test/benchmarks/larger-grammar/%s" % (filename) ]
    run_main('results/probe-larger.csv', filename, cmd)

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
    subparser.add_argument("--expt", type=str, default="perf")
    subparser = subparsers.add_parser("circuit", help="Run the BitVector Benchmark Programs")
    subparser.add_argument("--timeout", type = int, default = 600)
    subparser.add_argument("--memory", type = int, default = 16)
    subparser.add_argument("--strategy", type = str, default = "probe")
    subparser.add_argument("--expt", type=str, default="perf")
    return parser.parse_args()

args = parse_args()
times = args.timeout

def main():
    args = parse_args()
    if args.cmd in [ "string", "bitvec", "circuit"] and args.strategy in [ "probe", "size", "height" ] and args.expt in ["perf"]:
        run(args)
    elif args.cmd in [ "string", "bitvec", "circuit"] and args.strategy in [ "probe", "cvc4" ] and args.expt in ["accuracy"]:
        run_accuracy(args)
    elif args.cmd in [ "string", "bitvec", "circuit"] and args.strategy in [ "probe", "size", "height" ] and args.expt in ["sanity"]:
        run_sanity(args) 
    elif args.cmd in [ "string", "circuit"] and args.strategy in [ "probe", "size", "height" ] and args.expt in ["extgrammar"]:
        run_larger(args)     
    else:
        print("Invalid Argument")

if __name__ == "__main__":
    if os.path.exists('results/probe.csv') and args.expt in ["perf"] and args.strategy in ["probe"]:
        os.remove('results/probe.csv') 
    elif os.path.exists('results/size.csv') and args.expt in ["perf"] and args.strategy in ["size"]:
        os.remove('results/size.csv') 
    elif os.path.exists('results/height.csv') and args.expt in ["perf"] and args.strategy in ["height"]:
        os.remove('results/height.csv')
    elif os.path.exists('results/size-larger.csv') and args.expt in ["extgrammar"] and args.strategy in ["size"]:
        os.remove('results/size-larger.csv')
    elif os.path.exists('results/probe-larger.csv') and args.expt in ["extgrammar"] and args.strategy in ["probe"]:
        os.remove('results/probe-larger.csv')              
    elif os.path.exists('results/probe-accuracy.csv') and args.expt in ["accuracy"] and args.strategy in ["probe"]:
        os.remove('results/probe-accuracy.csv')  
    elif os.path.exists('results/cvc4-accuracy.csv') and args.expt in ["accuracy"] and args.strategy in ["cvc4"]:
        os.remove('results/cvc4-accuracy.csv')      
    elif os.path.exists('results/sanity.csv') and args.expt in ["sanity"]:
        os.remove('results/sanity.csv')               
    else:
        pass  
    main() 
