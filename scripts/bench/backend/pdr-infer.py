############ Do not change[start] ############
from common import *
############  Do not change[end]  ############

TARGET_NON_REACHABILITY = 'pdr-infer'
TARGET_NON_TERMINATION = 'infer-non-term'
cmd_template = 'ulimit -v 4194304 && {} {} {}'  # <option> <filename>

cfg = None


def pre_cmd():
    return ''


def config(c):
    global cfg
    cfg.base = 'ml'
    cfg = c


def cli_arg(parser):
    return parser


def gen_cmd(file):
    args = cfg.args
    ags = []

    ag = ' '.join(ags)
    target = TARGET_NON_REACHABILITY
    return cmd_template.format(target, ag, file)


def parse_stdout(stdout):
    result_data = dict()
    result_data['result'] = 'invalid' if 'Invalid' in stdout else 'valid' if 'Valid' in stdout else 'fail'
    return result_data


def callback(file, result):
    print(file)


def stat(results):
    print(results)

