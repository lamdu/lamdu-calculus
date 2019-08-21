c = open('dumps/test/benchmark.dump-simpl').read()

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
        if x == ')' or x == ',':
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

cant = set('''
>>=
<*>
<$
fmap
pure
leq
liftA2
'''.split())

ok = set('''
$fMonadPureInfer_$s$fMonadRWST_$c>>=
$fNFDataTypeError_$crnf
$fNFDataType_$crnf
$fOrdVar
$fUnifyPureInferType_$cunifyError
$fRecursiveUnify_$crecurse
[]
:
++
absentError
emptyScope
error
heq_sel
newMutVar#
pruneDeps1
readMutVar#
runMainIO1
rwhnf
seq#
unifyError
whnfIO'
writeMutVar#
'''.split())
ok.update(cant)

apps = set()
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
    if [x for x in w if x[:1].islower() or x in ['RealWorld', 'Any']]:
        # Skip specializations with type variables,
        # find only the top-level specializations
        continue
    apps.add((var, tuple(p)))

for var, p in sorted(apps):
    print(' '.join([var] + ['@'+x for x in p]))
