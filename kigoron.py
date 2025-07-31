def andI(p, q):
    if p[0] == "atom" and q[0] == "atom":
        return ("and", p[1], q[1])
    return None

def andE_left(expr):
    if expr[0] == "and":
        return ("atom", expr[1])
    return None

def andE_right(expr):
    if expr[0] == "and":
        return ("atom", expr[2])
    return None

def implyE(imp, fact):
    if imp[0] == "implies":
        antecedent = imp[1]
        if isinstance(antecedent, str):
            antecedent = ("atom", antecedent)
        if fact == antecedent:
            return imp[2]
    return None

def orI(p, side, other):
    if p[0] != "atom":
        return None
    if side == "left":
        return ("or", p[1], other)
    elif side == "right":
        return ("or", other, p[1])
    else:
        return None

def expr_to_str(expr):
    if expr[0] == "atom":
        return expr[1]
    elif expr[0] == "and":
        return f"({expr_to_str(('atom', expr[1]))} ∧ {expr_to_str(('atom', expr[2]))})"
    elif expr[0] == "implies":
        return f"({expr_to_str(expr[1])} → {expr_to_str(expr[2])})"
    elif expr[0] == "or":
        return f"({expr_to_str(('atom', expr[1]))} ∨ {expr_to_str(('atom', expr[2]))})"
    else:
        return str(expr)

def run_proof_with_full_log(premises, goal):
    proven = set(premises)
    changed = True
    log = []

    while changed:
        changed = False
        new_proven = set(proven)

        for expr in [p for p in proven if p[0] == "and"]:
            left = andE_left(expr)
            right = andE_right(expr)
            if left:
                log.append(f"  ∧除去(左): {expr_to_str(expr)} ⊢ {expr_to_str(left)} {'✔' if left not in proven else '(既出)'}")
                if left not in proven:
                    new_proven.add(left)
                    changed = True
            if right:
                log.append(f"  ∧除去(右): {expr_to_str(expr)} ⊢ {expr_to_str(right)} {'✔' if right not in proven else '(既出)'}")
                if right not in proven:
                    new_proven.add(right)
                    changed = True

        atoms = [p for p in proven if p[0] == "atom"]
        for p in atoms:
            for q in atoms:
                if p != q:
                    conj = andI(p, q)
                    if conj:
                        log.append(f"  ∧導入: {expr_to_str(p)}, {expr_to_str(q)} ⊢ {expr_to_str(conj)} {'✔' if conj not in proven else '(既出)'}")
                        if conj not in proven:
                            new_proven.add(conj)
                            changed = True

        for imp in [p for p in proven if p[0] == "implies"]:
            for fact in proven:
                result = implyE(imp, fact)
                if result:
                    if isinstance(result, str):
                        result = ("atom", result)
                    log.append(f"  →除去: {expr_to_str(imp)}, {expr_to_str(fact)} ⊢ {expr_to_str(result)} {'✔' if result not in proven else '(既出)'}")
                    if result not in proven:
                        new_proven.add(result)
                        changed = True

        if goal[0] == "or":
            left_goal, right_goal = goal[1], goal[2]
            for p in [e for e in proven if e[0] == "atom"]:
                left_expr = orI(p, "left", right_goal)
                right_expr = orI(p, "right", left_goal)

                if left_expr:
                    log.append(f"  ∨導入(左): {expr_to_str(p)} ⊢ {expr_to_str(left_expr)} {'✔' if left_expr == goal else '(失敗)'}")
                if right_expr:
                    log.append(f"  ∨導入(右): {expr_to_str(p)} ⊢ {expr_to_str(right_expr)} {'✔' if right_expr == goal else '(失敗)'}")

                if left_expr == goal and goal not in proven:
                    new_proven.add(goal)
                    changed = True
                if right_expr == goal and goal not in proven:
                    new_proven.add(goal)
                    changed = True

        proven = new_proven

    return log, goal in proven


if __name__ == "__main__":
    problem = {
        "name": "問題1（詳細ログ）",
        "premises": [
            ("atom", "P"),
            ("and", "Q", "R"),
            ("implies", ("and", "P", "Q"), "S")
        ],
        "goal": ("or", "S", "T")
    }

    log, success = run_proof_with_full_log(problem["premises"], problem["goal"])
    print(f"■ {problem['name']}: {expr_to_str(problem['goal'])}")
    for line in log:
        print(line)
    print("✔ 成功" if success else "✖ 失敗")
