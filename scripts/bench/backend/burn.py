############ Do not change[start] ############
from common import *
############  Do not change[end]  ############

TARGET = 'horus -rzs {} | z3 -smt2 -in'
cmd_template = TARGET

cfg = None


def pre_cmd():
    return 'ls' #nop


def config(c):
    global cfg
    cfg.base = 'hochcs'
    cfg = c


def cli_arg(parser):
    return parser


def gen_cmd(file):
    return cmd_template.format(file)


def parse_stdout(stdout):
    result_data = dict()
    l = stdout.split('\n')
    if len(l) == 1:
        result_data['result'] = 'fail'
        return result_data

    result = l[1]

    if result == 'sat':
        result_data['result'] = 'invalid'
    elif result == 'unsat':
        result_data['result'] = 'valid'
    else:
        result_data['result'] = 'unknown'

    return result_data


def callback(file, result):
    print(file)


def stat(results):
    print(results)

