#!/usr/bin/env python3
import sys
import json

# dataset identity
def ds_iden(x):
    l = x.split('/')
    if len(l) < 3:
        return x
    return '/'.join(l[-2:])


files = ['katsura.json', 'iwayama.json', 'suzuki.json']
def main():
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
            t = item['time'] if target == item['result'] else 6.0
            table[key].append(t)

    k_vs_i = (0, 0)
    k_vs_s = (0, 0)
    iwas = []
    suzs = []

    for key, row in table.items():
        (x, y) = k_vs_i
        if row[0] > row[1]:
            k_vs_i = (x, y + 1)
            iwas.append(key)
        else:
            k_vs_i = (x + 1, y)

        (x, y) = k_vs_s
        if row[0] > row[2]:
            k_vs_s = (x, y + 1)
            suzs.append(key)
        else:
            k_vs_s = (x + 1, y)

    print(f'Iwayamasan: {k_vs_i[0]} - {k_vs_i[1]}')

    for key in iwas:
        print(f'- {key}')
    print(f'Suzukisan: {k_vs_s[0]} - {k_vs_s[1]}')
    for key in suzs:
        print(f'- {key}')
main()

