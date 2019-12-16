import argparse
import os
import signal
import subprocess
import json

TARGET = 'dune exec hflmc2 -- '
TIMEOUT = 5  # sec

parser = argparse.ArgumentParser()
parser.add_argument("list", help="list which contains benchmarks")
parser.add_argument("--timeout", help="timeout", default=TIMEOUT, type=int)
parser.add_argument('--no-inline', action='store_true')
parser.add_argument('--json', help="set filename in which results will be saved", default=None)
parser.add_argument("--solver", help="set background CHC solver", default="auto")
parser.add_argument("--basedir", help="base directory", default="./inputs/")
args = parser.parse_args()

cmd_template = TARGET + ' {} {}'  # <option> <filename>


def run(cmd):
    with subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, preexec_fn=os.setsid) as p:
        try:
            output, _ = p.communicate(timeout=args.timeout)
            return output
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except:
                pass
            raise


def gen_cmd(file):
    ags = []
    if args.no_inline:
        ags.append('--no-inlining')
    s = args.solver
    if s == 'z3':
        ags.append("--solver z3")
    elif s == 'hoice':
        ags.append("--solver hoice")
    elif s == 'fptprove':
        ags.append("--solver fptprove")
    elif s == 'auto':
        ags.append("--solver auto")
    else:
        raise Exception('No such solver')

    ag = ' '.join(ags)
    return cmd_template.format(ag, file)



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
        elif 'Fail' in line:
            return 'fail'
        else:
            raise ParseError

    def parse_profile():
        line = readline()
        if 'total' in line:
            return float(line.replace(' ', '').replace('sec', '').split(':')[1])
        else:
            return parse_profile()

    result_data = dict()
    result_data['solver'] = 'fptprove' if 'Some definite clause has or-head' in stdout else 'z3'
    while cur < len(result):
        line = readline()
        if 'Verification Result:' in line:
            result_data['result'] = parse_verification_result()
        elif 'Profiling' in line:
            result_data['total'] = parse_profile()
        elif 'ill-typed' in line:
            result_data['ok'] = False
            result_data['error'] = 'ill-typed'
            return result_data
        else:
            pass
    # adhoc
    if 'result' in result_data and 'total' in result_data:
        result_data['ok'] = True
    else:
        result_data['error'] = 'unknown'
        result_data['ok'] = False
    return result_data


def p(file, result):
    if result['ok']:
        print(f'{file}\t{result["result"]}\t{result["total"]}\t{result["solver"]}')
    else:
        print(f'{file}\t{result["error"]}\t{TIMEOUT}\t{result["solver"]}')


def handle(file, callback=p):
    cmd = gen_cmd(file)
    try:
        stdout = run(cmd).decode('utf-8')
        result = parse_stdout(stdout)
    except subprocess.TimeoutExpired:
        result = {'ok': False, 'error': 'timeout'}
    callback(file, result)


results = []


def callback(file, result):
    p(file, result)
    result['file'] = file
    results.append(result)


def stat():
    valid_cnt = sum(1 for _ in filter(
        lambda x: 'result' in x and x['result'] == 'valid', results))
    invalid_cnt = sum(1 for _ in filter(
        lambda x: 'result' in x and x['result'] == 'invalid', results))
    timeout_cnt = sum(1 for _ in filter(
        lambda x: 'error' in x and x['error'] == 'timeout', results))

    no_errors = [x for x in results if x['ok']]
    mean = sum(x['total'] for x in no_errors) / len(no_errors)
    print('[Result]')
    print(f'- solver={args.solver}')
    print(f'- valid={valid_cnt}')
    print(f'- invalid={invalid_cnt}')
    print(f'- timeout={timeout_cnt}')
    print(f'- mean_without_errors={mean}')


def save_json(filename):
    with open(filename, "w") as f:
        json.dump(results, f)

def main():
    with open(args.list) as f:
        files = f.read().strip('\n').split('\n')
    for file in files:
        handle(os.path.join(args.basedir, file), callback=callback)
    stat()
    if args.json is not None:
        save_json(args.json)

main()
