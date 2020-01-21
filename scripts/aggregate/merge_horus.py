
import json
fhorus = 'horus.csv'
fhorus_cps = 'horus_cps.csv'

fkatsura = 'katsura.json'
fz3 = 'burn2-z3.json'
fmz3= 'mochi-z3.json'

id_burn1 = '/Burn_POPL18/'
id_burn2 = 'Burn_POPL18_2'
id_mochi = 'mochi'

# dataset identity
def identity(x):
    l = x.split('/')
    name = l[-1]
    return name.replace('.in', '')

def result(x):
    r = x['result']
    t = x['time']
    if r == 'valid':
        return t
    if r == 'invalid':
        return 100
    if r == 'fail':
        return 10
    return t

def json_load(name):
    with open(name, 'r') as f:
        data = json.load(f)
    return data

def gen_result(name, result):
    if result == 'error':
        return False, 0
    if name.endswith('-e'):
        return False, 0
    if result == 'unknown':
        return True, 100.0
    if result == 'timeout':
        return True, 10.0
    return True, result

def csv_load(name):
    data = []
    with open(name, 'r') as f:
        for line in f.read().strip('\n').split('\n'):
            line = line.split(',')
            flag, result = gen_result(line[0], line[1])
            if not flag:
                continue
            data.append({'name': line[0], 'result': result})
    return data

def exp(burn1, horus, filename):
    data = []
    for x in horus:
        name = x['name']
        r_h = x['result']
        r_k = None
        for y in burn1:
            if name == y['name']:
                r_k = y['result']
                break
        if r_k is None:
            print('not found ' + name)
            continue
        data.append(','.join(map(str, [name, r_k, r_h])))
    with open(filename, 'w') as f:
        f.write('\n'.join(data))

def fil(data, id):
    return list(filter(lambda x: id in x['file'], data))

def projection(data):
    return [
            {'name': identity(x['file']),
             'result': result(x),
            } for x in data
            ]

def main():
    katsura = json_load(fkatsura)
    horus = csv_load(fhorus)
    horus_cps = csv_load(fhorus_cps)
    burn1 = projection(fil(katsura, id_burn1))
    burn2 = projection(fil(katsura, id_burn2))
    mochi = projection(fil(katsura, id_mochi))
    exp(burn1, horus, 'katsura-horus1.csv')
    exp(burn2, horus, 'katsura-horus2.csv')
    exp(mochi, horus_cps, 'katsura-horus3.csv')

    burn2_z3 = json_load(fz3)
    burn2_z3 = projection(fil(burn2_z3, id_burn2))
    exp(burn2_z3, horus, 'katsura-horus2-z3.csv')

    mochi_z3 = json_load(fmz3)
    mochi_z3 = projection(fil(mochi_z3, id_mochi))
    exp(mochi_z3, horus_cps, 'katsura-horus3-z3.csv')

main()
