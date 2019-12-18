import os

base = os.path.dirname(os.path.abspath(__file__))
repo = os.path.dirname(os.path.dirname(base))

START = '############ Do not change[start] ############\n'
END = '############  Do not change[end]  ############\n'
COMMON = '############ Do not change[common] ############\n'
TARGET = '############ Do not change[target] ############\n'
BASE = '############ Do not change[base] ############\n'


def read_file(filename):
    path = os.path.join(base, filename)
    with open(path, 'r') as f:
        content = ''
        flag = False
        while True:
            l = f.readline()
            if l == '':
                break
            if l == START:
                flag = True
            elif l == END:
                flag = False
                break
            if not flag:
                content += l

        content += f.read()
    return content

common = read_file('common.py')
target = read_file('bench.py')

target = target.replace(COMMON, common)
target = target.replace(BASE, f'base = "{os.path.join(repo, "benchmark")}"\n')

benchdir = os.path.join(base, 'benchmark')
try:
    os.makedirs(benchdir)
except FileExistsError:
    pass

benchmarkers = os.listdir(os.path.join(base, 'backend'))
for benchmark in benchmarkers:
    file = read_file('backend/' + benchmark)

    generated = target.replace(TARGET, file)
    with open(os.path.join(benchdir, benchmark), 'w') as f:
        f.write(generated)