############ Do not change[start] ############
from common import *
############  Do not change[end]  ############

# assumption: this script is placed at <project_root>/scripts
project_root = os.path.realpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../'))
base = os.path.join(project_root, './benchmark')
TARGET = '../target/release/check'
cmd_template = TARGET + ' {} --input {}'  # <option> <filename>

cfg = None


def pre_cmd():
    return 'cargo build --release'


def config(c):
    global cfg
    cfg = c


def cli_arg(parser):
    return parser


def gen_cmd(file):
    args = []
    if file.endswith('.smt2'):
        args.append("--chc")
    ag = ' '.join(args)
    return cmd_template.format(ag, file)


def parse_stdout(stdout):
    result_data = dict()
    result_data['result'] = 'invalid' if 'Invalid' in stdout else 'unknown' if 'Unknown' in stdout else 'fail'
    return result_data

def p(file, result):
    if result['ok']:
        print(f'{file}\t{result["result"]}\t{result["total"]}\t{result["solver"]}')
    else:
        print(f'{file}\t{result["error"]}\t{cfg.args.timeout}\t{result["solver"]}')


def callback(file, result):
    print(file)

def stat(results):
    print(results)
