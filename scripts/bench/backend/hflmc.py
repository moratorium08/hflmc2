############ Do not change[start] ############
from common import *
############  Do not change[end]  ############

TARGET = '../target/release/hflmc '
cmd_template = TARGET + ' {} {}'  # <option> <filename>

cfg = None


def pre_cmd():
    return 'cargo build --release'


def config(c):
    global cfg
    cfg.retry = 3
    cfg = c


def cli_arg(parser):
    parser.add_argument('--no-inline', action='store_true')
    return parser


def gen_cmd(file):
    args = cfg.args
    ags = []
    ags.append('--hc-solver rcaml')
    ags.append('--z3-path /home/katsura/misc/hflmc/bin/z3')
    if args.no_inline:
        ags.append('--no-inlining')

    ag = ' '.join(ags)
    return cmd_template.format(ag, file)


def parse_stdout(stdout):
    result_data = dict()
    result_data['result'] = 'invalid' if 'UnSat' in stdout else 'valid' if 'Sat' in stdout else 'fail'
    return result_data


def callback(file, result):
    print(file)


def stat(results):
    print(results)

