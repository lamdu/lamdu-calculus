c = open('test/benchmark.dump-simpl').read()

c = c.split('------ Local rules for imported ids --------', 1)[0]

def normalize(x):
    x = x.strip().replace('\n', ' ')
    while '  ' in x:
        x = x.replace('  ', ' ')
    return x

def take_word():
    global c
    stack = []
    for i, x in enumerate(c):
        if stack and x == stack[-1]:
            stack.pop()
            continue
        if x == ')':
            break
        if x == '(':
            stack.append(')')
            continue
        if x == '[':
            stack.append(']')
            continue
        if x == ' ' and not stack:
            break
    r = normalize(c[:i])
    c = c[i:].strip()
    return r

def params():
    global c
    r = [take_word()]
    while c.startswith('@'):
        c = c[1:].strip()
        r.append (take_word())
    return r

def last_word(d):
    stack = []
    for i, x in enumerate(d[::-1]):
        if stack and x == stack[-1]:
            stack.pop()
            continue
        if x == '(':
            break
        if x == ')':
            stack.append('(')
            continue
        if x == ']':
            stack.append('[')
            continue
        if x == ' ' and not stack:
            break
    return normalize(d[-i:])

apps = set()

ok = set('''
[]
:
++
>>=
$wpruneDeps
absentError
emptyScope
error
fmap
heq_sel
newMutVar#
pure
pureK
readMutVar#
runMainIO1
rwhnf
seq#
whnfIO'
writeMutVar#
'''.split())

while '@' in c:
    pre, post = c.split('@', 1)
    c = post.strip()
    if pre.strip().endswith('\\'):
        # Lambda. Skip type parameters
        params()
        continue
    if post.startswith('~'):
        # Not a type application
        continue
    var = last_word(pre.strip())
    while var.startswith('('):
        var = var[1:]
    p = params()
    if var[:1].isupper():
        # Skip data constructors
        continue
    if var in ok:
        continue
    w = []
    for x in p:
        w += x.replace('(', ' ').replace('[', ' ').split()
    if [x for x in w if x[:1].islower() or x == 'RealWorld']:
        # Skip specializations with type variables,
        # find only the top-level specializations
        continue
    apps.add((var, tuple(p)))

for var, p in sorted(apps):
    print(' '.join([var] + ['@'+x for x in p]))
