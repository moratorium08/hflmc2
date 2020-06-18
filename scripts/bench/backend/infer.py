############ Do not change[start] ############
from common import *
############  Do not change[end]  ############

TARGET_NON_REACHABILITY = 'infer'
TARGET_NON_TERMINATION = 'infer-non-term'
cmd_template = '{} {} {}'  # <option> <filename>

cfg = None


def pre_cmd():
    return ''


def config(c):
    global cfg
    cfg.base = 'ml'
    cfg = c


def cli_arg(parser):
    parser.add_argument('--no-inline', action='store_true')
    parser.add_argument('--non-termination', action='store_true')
    return parser


def gen_cmd(file):
    args = cfg.args
    ags = []
    if args.no_inline:
        ags.append('--no-inlining')
    if args.non_termination:
        target = TARGET_NON_TERMINATION
    else:
        target = TARGET_NON_REACHABILITY

    ag = ' '.join(ags)
    return cmd_template.format(target, ag, file)


def parse_stdout(stdout):
    result_data = dict()
    result_data['result'] = 'invalid' if 'Invalid' in stdout else 'valid' if 'Valid' in stdout else 'fail'
    return result_data


def callback(file, result):
    print(file)


def stat(results):
    print(results)
