import argparse
import os
import signal
import subprocess

TARGET = './_build/default/bin/main.exe'
TIMEOUT = 5 # sec

parser = argparse.ArgumentParser()
parser.add_argument("solver", help="set background CHC solver")
parser.add_argument("benchdir", help="directory which contains benchmarks")
args = parser.parse_args()

cmd_template = TARGET + ' --solver {} {}'

def run(cmd):
    with subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, preexec_fn=os.setsid) as p:
        try:
            output, _ = p.communicate(timeout=TIMEOUT)
            return output
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except:
                pass
            raise

def gen_cmd(file):
    s = args.solver
    if s == 'z3':
        return cmd_template.format("z3", file)
    elif s == 'hoice':
        return cmd_template.format("hoice", file)
    elif s == 'fptprove':
        return cmd_template.format("fptprove", file)
    else:
        raise Exception('No such solver')

class ParseError(Exception):
    pass

def parse_stdout(stdout):
    idx = stdout.find('Verification Result:')
    result = stdout[idx:].split('\n')
    cur = 0
    def readline():
        nonlocal cur
        line = result[cur]
        cur += 1
        return line

    def parse_verification_result():
        line = readline()
        if 'Invalid' in line:
            return 'invalid'
        elif 'Valid' in line:
            return 'valid'
        else:
            raise ParseError
    
    def parse_profile():
        line = readline()
        if 'total' in line:
            return float(line.replace(' ', '').replace('sec', '').split(':')[1])
        else:
            return parse_profile()

    result_data = dict()
    while cur < len(result):
        line = readline()
        if 'Verification Result:' in line:
            result_data['result'] = parse_verification_result()
        elif 'Profiling' in line:
            result_data['total'] = parse_profile()
        else:
            pass
    return result_data

def p(file, result):
    if result['ok']:
        print(f'{file}\t{result["result"]}\t{result["total"]}')
    else:
        print(f'{file}\t{result["error"]}')

def handle(file, callback=p):
    cmd = gen_cmd(file)
    try:
        stdout = run(cmd).decode('utf-8')
        result = parse_stdout(stdout)
        result['ok'] = True
    except subprocess.TimeoutExpired:
        result = {'ok': False, 'error': 'timeout'}
    p(file, result)

def main():
    files = os.listdir(args.benchdir)
    for file in files:
        if file.endswith('.in'):
            handle(os.path.join(args.benchdir, file))

main()