############ Do not change[start] ############
from common import *
############  Do not change[end]  ############

TARGET = 'mochi -only-result'
cmd_template = TARGET + ' {} {}'  # <option> <filename>

cfg = None


def pre_cmd():
    return ''


def config(c):
    global cfg
    cfg.base = 'ml'
    cfg = c


def cli_arg(parser):
    parser.add_argument('--non-termination', action='store_true')
    return parser


def gen_cmd(file):
    args = cfg.args
    ags = []
    if args.non_termination:
        ags.append('-non-termination')
    ag = ' '.join(ags)
    return cmd_template.format(ag, file)


def parse_stdout(stdout):
    result_data = dict()
    result_data['result'] = 'invalid' if 'Unsafe' in stdout else 'valid' if 'Safe' in stdout else 'fail'
    return result_data


def callback(file, result):
    print(file)


def stat(results):
    print(results)
