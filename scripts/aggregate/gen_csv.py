#!/usr/bin/env python3
import sys
import json

TIMEOUT_T = 180
FAIL_T = -1
# dataset identity
def ds_iden(x):
    l = x.split('/')
    if len(l) < 3:
        return x
    return '/'.join(l[-2:])


def main():
    if sys.argv[0] == 'python':
        files = sys.argv[2:]
    else:
        files = sys.argv[1:]

    if len(files) == 0:
        print('input json files as cli arguments')
        return

    datas = []
    for f in files:
        with open(f, 'r') as f:
            data = json.load(f)
            datas.append(data)

    keys = [ds_iden(x['file']) for x in datas[0]]
    table = dict()
    for key in keys:
        table[key] = []

    for data in datas:
        for item in data:
            key = ds_iden(item['file'])
            target = 'invalid' if key.endswith('-e.in') else 'valid'
            t = item['time'] if target == item['result'] else FAIL_T
            if item['time'] >= TIMEOUT_T - 0.001:
                t = TIMEOUT_T
            table[key].append(t)

    for key, row in table.items():
        print(f"{key}, {', '.join(map(str, row))}")

main()

