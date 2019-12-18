import argparse
import os
import signal
import subprocess
import json
import time

############ Do not change[base] ############
############ Do not change[common] ############
############ Do not change[target] ############

############ Do not change[start] ############
base = "./"
from common import *
from target import cli_arg, gen_cmd, parse_stdout, config, callback, stat, pre_cmd
############  Do not change[end]  ############

TIMEOUT = 5

class Config:
    def __init__(self):
        pass

parser = argparse.ArgumentParser()
parser.add_argument("list", help="benchmark target name")
parser.add_argument("--timeout", help="timeout", default=TIMEOUT, type=int)
parser.add_argument('--json', help="set filename in which results will be saved", default=None)
parser.add_argument("--basedir", help="base directory", default=base)
parser = cli_arg(parser)
args = parser.parse_args()

cfg = Config()
cfg.args = args
config(cfg)


def run(cmd, timeout=None):
    if timeout is None:
        timeout=args.timeout
    st = time.perf_counter()
    with subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, preexec_fn=os.setsid) as p:
        try:
            output, _ = p.communicate(timeout=timeout)
            ed = time.perf_counter()
            elapsed = ed - st
            return output, elapsed
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except:
                pass
            raise


def p(file, result):
    print(result)


results = []
def handle(file, parser, callback=p):
    cmd = gen_cmd(file)
    try:
        stdout, t = run(cmd)
        stdout = stdout.decode('utf-8')
        result = parser(stdout)
        result['time'] = t
    except subprocess.TimeoutExpired:
        result = {'ok': False, 'error': 'timeout'}
        result['time'] = args.timeout
    if 'result' not in result:
        result['result'] = 'fail'
    result['file'] = file
    callback(file, result)
    results.append(result)


def save_json(filename):
    with open(filename, "w") as f:
        json.dump(results, f)


def main():
    out, _ = run(pre_cmd(), timeout=1000)
    print(out)
    with open(os.path.join(args.basedir, 'lists', args.list)) as f:
        files = f.read().strip('\n').split('\n')
    for file in files:
        handle(os.path.join(args.basedir, 'inputs', file), parse_stdout, callback=callback)
    stat(results)
    if args.json is not None:
        save_json(args.json)

main()
