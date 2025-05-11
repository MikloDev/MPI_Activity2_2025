import time
import tracemalloc
import random
import concurrent.futures
from copy import deepcopy

def parse_cnf(clauses):
    return [set(clause) for clause in clauses]

def is_unit(clause):
    return len(clause) == 1

def unit_propagate(clauses, assignment):
    changed = True
    while changed:
        changed = False
        unit_clauses = [c for c in clauses if is_unit(c)]
        for unit in unit_clauses:
            literal = next(iter(unit))
            if -literal in assignment:
                return False, assignment
            if literal not in assignment:
                assignment.add(literal)
                changed = True
                clauses = simplify(clauses, literal)
    return clauses, assignment

def simplify(clauses, literal):
    new_clauses = []
    for clause in clauses:
        if literal in clause:
            continue
        if -literal in clause:
            new_clause = clause - {-literal}
            new_clauses.append(new_clause)
        else:
            new_clauses.append(clause)
    return new_clauses

def choose_literal(clauses, strategy='random'):
    flat_literals = [lit for clause in clauses for lit in clause]
    if strategy == 'random':
        return random.choice(flat_literals)
    elif strategy == 'dlis':
        counts = {}
        for clause in clauses:
            for lit in clause:
                counts[lit] = counts.get(lit, 0) + 1
        return max(counts, key=counts.get)
    else:
        return flat_literals[0]

def dpll(clauses, assignment=set(), strategy='random'):
    clauses, assignment = unit_propagate(clauses, assignment)
    if clauses is False:
        return False
    if not clauses:
        return assignment
    literal = choose_literal(clauses, strategy)
    for val in [literal, -literal]:
        new_clauses = simplify(deepcopy(clauses), val)
        result = dpll(new_clauses, assignment | {val}, strategy)
        if result:
            return result
    return False

def dp(clauses):
    vars_ = set(abs(lit) for clause in clauses for lit in clause)
    while vars_:
        var = vars_.pop()
        pos_clauses = [c for c in clauses if var in c]
        neg_clauses = [c for c in clauses if -var in c]
        new_clauses = []
        for c1 in pos_clauses:
            for c2 in neg_clauses:
                res = (c1 | c2) - {var, -var}
                if not res:
                    return False
                new_clauses.append(res)
        clauses = [c for c in clauses if var not in c and -var not in c] + new_clauses
    return True

def resolution(clauses):
    clauses = list(map(set, clauses))
    new = set()
    while True:
        n = len(clauses)
        for i in range(n):
            for j in range(i+1, n):
                resolvents = resolve(clauses[i], clauses[j])
                if set() in resolvents:
                    return False
                new.update(resolvents)
        if new.issubset(set(map(frozenset, clauses))):
            return True
        for c in new:
            if c not in clauses:
                clauses.append(c)

def resolve(c1, c2):
    resolvents = set()
    for lit in c1:
        if -lit in c2:
            res = (c1 | c2) - {lit, -lit}
            resolvents.add(frozenset(res))
    return resolvents

def generate_random_3sat(num_vars, num_clauses):
    cnf = []
    for _ in range(num_clauses):
        clause = set()
        while len(clause) < 3:
            var = random.randint(1, num_vars)
            lit = var if random.choice([True, False]) else -var
            clause.add(lit)
        cnf.append(list(clause))
    return parse_cnf(cnf)

def run_solver(solver_fn, clauses, name, strategy=None, timeout_sec=10):
    def task():
        if strategy:
            return solver_fn(deepcopy(clauses), set(), strategy)
        else:
            return solver_fn(deepcopy(clauses))

    tracemalloc.start()
    start = time.time()

    with concurrent.futures.ThreadPoolExecutor() as executor:
        future = executor.submit(task)
        try:
            result = future.result(timeout=timeout_sec)
            timed_out = False
        except concurrent.futures.TimeoutError:
            result = None
            timed_out = True

    end = time.time()
    mem = tracemalloc.get_traced_memory()[1] / 1024 / 1024
    tracemalloc.stop()

    if timed_out:
        print(f"{name:<10} | Time: >{timeout_sec}s | Memory: {mem:.2f}MB | Result: TIMEOUT\n")
    elif isinstance(result, set):
        assignment = sorted(result, key=lambda x: abs(x))
        print(f"{name:<10} | Time: {end - start:.4f}s | Memory: {mem:.2f}MB | Result: SAT")
        print(f"Assignment: {assignment}\n")
    elif result is True:
        print(f"{name:<10} | Time: {end - start:.4f}s | Memory: {mem:.2f}MB | Result: SAT (no assignment shown)\n")
    else:
        print(f"{name:<10} | Time: {end - start:.4f}s | Memory: {mem:.2f}MB | Result: UNSAT\n")

example_cnf = parse_cnf([
    [1, -3, 4],
    [-1, 2],
    [-2, 3],
    [-4]
])

random_cnf = generate_random_3sat(10, 40)
print("Random CNF clauses:\n")
for clause in random_cnf:
    print(clause)

print("\nRunning on example CNF:\n")
run_solver(resolution, example_cnf, "Resolution")
run_solver(dp, example_cnf, "Davis-Putnam")
run_solver(dpll, example_cnf, "DPLL-Random", strategy='random')
run_solver(dpll, example_cnf, "DPLL-DLIS", strategy='dlis')

print("Running on random 3-SAT instance:\n")
run_solver(resolution, random_cnf, "Resolution")
run_solver(dp, random_cnf, "Davis-Putnam")
run_solver(dpll, random_cnf, "DPLL-Random", strategy='random')
run_solver(dpll, random_cnf, "DPLL-DLIS", strategy='dlis')