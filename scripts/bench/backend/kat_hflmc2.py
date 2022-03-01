############ Do not change[start] ############
from common import *
############  Do not change[end]  ############

TARGET = './_build/default/bin/main.exe '
cmd_template = TARGET + ' {} {}'  # <option> <filename>

cfg = None


def pre_cmd():
    return 'dune build'


def config(c):
    global cfg
    c.root = '../'
    cfg = c


def cli_arg(parser):
    parser.add_argument("--solver", help="set background CHC solver", default="auto")
    parser.add_argument('--no-inline', action='store_true')
    parser.add_argument('--mode-burn-et-al', action='store_true')
    parser.add_argument('--no-disprove', action='store_true')
    parser.add_argument('--remove-disjunction', action='store_true')
    return parser


def gen_cmd(file):
    args = cfg.args
    ags = []
    if args.no_inline:
        ags.append('--no-inlining')
    if args.mode_burn_et_al:
        ags.append('--mode-burn-et-al')
    if args.remove_disjunction:
        ags.append('--remove-disjunction')
    if args.no_disprove:
        ags.append('--no-disprove')
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
        elif 'Unknown' in line:
            return 'unknown'
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
        print(f'{file}\t{result["error"]}\t{cfg.args.timeout}\t{result["solver"]}')


def callback(file, result):
    p(file, result)


def stat(results):
    valid_cnt = sum(1 for _ in filter(
        lambda x: 'result' in x and x['result'] == 'valid', results))
    invalid_cnt = sum(1 for _ in filter(
        lambda x: 'result' in x and x['result'] == 'invalid', results))
    timeout_cnt = sum(1 for _ in filter(
        lambda x: 'error' in x and x['error'] == 'timeout', results))

    no_errors = [x for x in results if x['ok']]
    #mean = sum(x['total'] for x in no_errors) / len(no_errors)
    print('[Result]')
    print(f'- solver={cfg.args.solver}')
    print(f'- valid={valid_cnt}')
    print(f'- invalid={invalid_cnt}')
    print(f'- timeout={timeout_cnt}')
    #print(f'- mean_without_errors={mean}')
