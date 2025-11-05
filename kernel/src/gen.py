def generate_abs(n):
    if n == 1:
        args_str = '$arg'
        goals = '(goal $arg)'
    else:
        args_list = [f'$arg{i}' for i in range(1, n+1)]
        args_str = ' '.join(args_list)
        goals = ' '.join(f'(goal {arg})' for arg in args_list)
    kb = f'(kb ((({args_str}) $dep) -> $ccls))'
    left = f'(, (goal $ccls) {kb} )'
    ev = f'(ev ((({args_str}) $dep) -> $ccls))'
    right = f'(, {ev} {goals} )'
    return f'((step abs{n})\n  {left}\n  {right} )'

def generate_app(a, d):
    arg_list = [f'$arg{i}' for i in range(1, a+1)]
    args_str = ' '.join(arg_list)
    ev_args = ' '.join(f'(ev {arg})' for arg in arg_list)
    if d == 0:
        dep_struct = 'Empty'
        right = '(ev $r)'
        right_goals = ''
    else:
        if d == 1:
            darg_list = ['$deparg1']
        else:
            darg_list = [f'$darg{i}' for i in range(1, d+1)]
        dargs_str = ' '.join(darg_list)
        dep_struct = f'(({dargs_str}) $dep)'
        right = f'(ev ( {dep_struct} -> $r ))'
        right_goals = ' ' + ' '.join(f'(goal {darg})' for darg in darg_list)
    left_ev = f'(ev ((({args_str}) ({dep_struct})) -> $r))'
    left = f'(, {left_ev} {ev_args})'
    right_full = f'(, {right}{right_goals} )'
    return f'((step app{a}_{d})\n  {left}\n  {right_full} )'

# Examples: modify or add calls here to generate others
print(generate_abs(3))
print('\n')
print(generate_app(3,0))
print('\n')
print(generate_app(3,1))
print('\n')
print(generate_app(3,2))
print('\n')
print(generate_app(3,3))
print('\n')
print(generate_abs(4))
print('\n')
print(generate_app(4,0))
print('\n')
print(generate_app(4,1))
print('\n')
print(generate_app(4,2))
print('\n')
print(generate_app(4,3))
