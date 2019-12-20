############ Do not change[start] ############
from common import *
############  Do not change[end]  ############

TARGET = '../_build/default/bin/main.exe '
cmd_template = TARGET + ' {} {}'  # <option> <filename>

cfg = None

def config(c):
    global cfg
    cfg = c


def pre_cmd():
    return 'dune build'


def cli_arg(parser):
    parser.add_argument('--no-inline', action='store_true')
    return parser


def gen_cmd(file):
    args = cfg.args
    ags = []
    if args.no_inline:
        ags.append('--no-inlining')

    ag = ' '.join(ags)
    return cmd_template.format(ag, file)


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

    result_data = dict()
    while cur < len(result):
        line = readline()
        if 'Verification Result:' in line:
            result_data['result'] = parse_verification_result()
        elif 'ill-typed' in line:
            result_data['ok'] = False
            result_data['error'] = 'ill-typed'
            return result_data
        else:
            pass
    if 'result' not in result_data:
        result_data['error'] = 'unknown'
    return result_data


def callback(file, result):
    print(file)


def stat(results):
    print(results)
