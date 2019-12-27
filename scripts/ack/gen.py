from sexpdata import loads, dumps, Symbol

def sl(l):
    return l

def x0(args):
    return True

def x1(args):
    return sl([Symbol('>'), args[0], args[1]])

def x2(args):
    return True

def x3(args):
    return sl([Symbol('>'), args[0], args[1]])

def x16(args):
    return True

def x17(args):
    return sl([Symbol('='), args[0], 0])

def x18(args):
    return sl([Symbol('<'), sl([Symbol('-'), args[1], 1]), args[0]])

def x19(args):
    return sl([Symbol('and'), sl([Symbol('not'), [Symbol('='), args[0], 0]]), sl([Symbol('not'), [Symbol('='), args[1], 0]])])

m = {
    'X0': x0,
    'X1': x1,
    'X2': x2,
    'X3': x3,
    'X16': x16,
    'X17': x17,
    'X18': x18,
    'X19': x19,
}
def replace(item):
    if type(item) != list:
        return item
    v = item[0].value()
    if v in m:
        return [Symbol('not'), m[v](item[1:])]
    else:
        return list(map(replace, item))

def main():
    with open('ack.in', 'r') as f:
        l = loads('(' + f.read() + ')')

    r = []
    r.append(l[0])
    for item in l:
        if 'assert' == item[0].value():
            item[1][2] = replace(item[1][2])
            r.append(item)

    r.append(l[-1])
    with open('ack_modified.in', 'w') as f:
        f.write(dumps(r, true_as='true')[1:-1])
main()