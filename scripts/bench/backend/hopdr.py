############ Do not change[start] ############
from common import *
############  Do not change[end]  ############

TARGET = '../target/release/hopdr'
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
    #args = cfg.args
    #ag = ' '.join(args)
    ag = ''
    return cmd_template.format(ag, file)


def parse_stdout(stdout):
    result_data = dict()
    result_data['result'] = 'invalid' if 'Invalid' in stdout else 'valid' if 'Valid' in stdout else 'fail'
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
