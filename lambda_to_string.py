import dis
import re
from io import StringIO

def lambda_to_string(l):
    """
    Convert a lambda function to its string representation by examining its bytecode.
    Mostly designed for expressions similar to lambda calculus, so this only works with a subset of bytecode.
    """
    disl = ""
    with StringIO() as out:
        dis.dis(l, file=out)
        disl += out.getvalue()
    strings = re.split( r"\nDisassembly of .+? at ([0-9a-fA-Fx]+), .+?\n", disl)
    addr = "main"
    code = {}
    for n, i in enumerate(strings):
        if n & 1 == 1:
            addr = i
        else:
            code[addr] = i
    return parse_bytecode("main", code, l.__code__, l.__closure__)

global_cache = {}
def load_global(name):
    """
    Load a global variable by name and return its string representation.
    If the global variable is already cached, return the cached value.
    """
    if not(name in globals()):
        return name
    if name in global_cache:
        return global_cache[name]
    res = lambda_to_string(globals()[name])
    global_cache[name] = res
    return res

def needs_parentheses(s):
    """
    Determine if a string representation of an expression needs parentheses.
    """
    s = str(s)
    # variables, numbers, and strings don't need parentheses
    if re.search(r"^\w+(?:\([^)]*\))?$", s) or re.search(r"^\d+(?:\.\d+)?$", s) or re.search(r"^\".+\"$", s) or re.search(r"^'.+'$", s):
        return False
    # comparison operators don't need parentheses if both sides are simple enough
    comp = re.search(r"^(['\"]?[a-zA-Z0-9_.]*['\"]?)(?:==|!=|<|>|<=|>=)(['\"]?[a-zA-Z0-9_.]*['\"]?)$", s);
    if comp != None and not(needs_parentheses(comp.group(1)) and not(needs_parentheses(comp.group(2)))):
        return False
    return True

def parse_bytecode(addr, code, cobj, closure = [], retMode = False):
    """
    Parse the bytecode of a function and return its string representation.

    addr: The address of the function in the code dictionary.
    code: A dictionary mapping addresses to disassembled bytecode strings.
    cobj: The code object of the function.
    closure: A list of closure variables for the function.
    retMode: If True, return on RETURN_VALUE and don't wrap the result in a lambda function.
    """
    variables = {}
    stack = []
    # keep track of nested ternary operators
    ternaryState = 0
    if retMode:
        func = addr
        variables = code
    else:
        func = code[addr]
    lines = func.split('\n')
    if closure:
        closure = list(closure)
    for n, line in enumerate(lines):
        if len(line) == 0:
            continue
        lineMatch = re.search(r'[0-9\-]*\s*([A-Z_]+)\s*(\d+)?(?: \((.+?)\)| <(.+?)>)?', line)
        if lineMatch == None:
            print(line)
            continue
        instr, idx, name = lineMatch.group(1, 2, 3)
        if idx:
            idx = int(idx)
        match instr:
            # load_closure but nonchalant
            case "LOAD_DEREF":
                variables[idx] = name
                stack.append(variables[name])

            # load boring stuff
            case "LOAD_FAST":
                variables[idx] = name
                variables[name] = name
                stack.append(name)

            # idk if this is actually a load_fast or secretly a load_deref
            case "LOAD_FAST_BORROW":
                if name in variables:
                    variables[idx] = name
                    stack.append(variables[name])
                    continue
                variables[idx] = name
                variables[name] = name
                stack.append(name)

            case "CALL":
                a = stack.pop()
                b = stack.pop()
                if needs_parentheses(b):
                    b = f"({b})"
                stack.append(f"{b}({a})")

            # this one is fun because it lets us use things from multiple lambdas together
            case "LOAD_GLOBAL":
                matchName = re.search(r"(\w+)(?: + NULL)?", name)
                if matchName == None:
                    print("load_global", name, "failed ??")
                    continue
                stack.append(load_global(matchName.group(0)))

            # this passes a bound variable into the inner functions
            # we don't really need it here
            case "MAKE_CELL":
                variables[name] = name

            # i didn't actually look to see if the python interpreter does this but here it would mess everything up
            case "PUSH_NULL":
                pass

            # this is used for numbers and lambda objects
            case "LOAD_CONST":
                matchConst = re.search(r" at ([0-9a-fA-Fx]+),", name)
                if matchConst == None:
                    # assume it's a number :P
                    stack.append(name)
                    continue
                const = matchConst.group(1)
                stack.append(const)

            # turn constant lambda pointer into function
            # different python versions have different bytecode here (yay!)
            case "MAKE_FUNCTION":
                const = stack.pop()
                stuff = []
                if idx == None:
                    nextLine = lines[n + 1]
                    nextMatch = re.search(r'[0-9\-]*\s*([A-Z_]+)\s*(\d+)?(?: \((.+).$| <(.+).$)?', nextLine)
                    if nextMatch != None:
                        nextInstr, nextIdx, nextName = nextMatch.group(1, 2, 3)
                        if nextInstr == "SET_FUNCTION_ATTRIBUTE":
                            idx = int(nextIdx)
                        else:
                            idx = 0
                    else:
                        idx = 0
                if int(idx) > 0:
                    stuff = stack.pop()
                funct = list(filter(lambda i: const in str(i), list(cobj.co_consts)))
                # no way two functions have the same memory address
                funct = funct[0]
                stack.append(parse_bytecode(const, code, funct, stuff[::-1]))

            # load variable from closure
            case "LOAD_CLOSURE":
                stack.append(variables[name])
                variables[idx] = name

            # i don't remember if this actually matters or not but in theory it's used for sending context to inner lambdas
            case "BUILD_TUPLE":
                tup = []
                for i in range(idx):
                    v = stack.pop()
                    if v.isidentifier():
                        tup.append(variables[v])
                    else:
                        tup.append(v)
                stack.append(tuple(tup))

            # lambda.__code__ is static, so this is how we get the context and what makes this different from other methods
            case "COPY_FREE_VARS":
                for i in range(idx):
                    if isinstance(closure[i], str):
                        variables[cobj.co_freevars[i]] = closure[i]
                    else:
                        variables[cobj.co_freevars[i]] = lambda_to_string(closure[i].cell_contents)

            # used for all binary operators which unfortunately includes a[b] and all other forms, which we have to detect
            case "BINARY_OP":
                a = str(stack.pop())
                b = stack.pop()
                if name == '[]':
                    # b[a]
                    if re.search(r"^\d+$", a) or re.search(r"^(\"|\').+?\1$", a):
                        stack.append(f"{b}[{a}]")
                    # b.something(a) (technically the full function name and constant arguments are contained in a)
                    elif re.search(r"^\w+\(", a):
                        op = re.search(r"^(\w+)\(", a).group(1)
                        # sadly there's no dunder method for slice
                        if op == "slice":
                            sliceMatch = re.search(r"slice\((.+?), (.+?), (.+)", a)
                            if sliceMatch != None:
                                d, e, f = sliceMatch.group(1, 2, 3)
                                stack.append(f"{b}[{d if d != "None" else ""}:{e if e != "None" else ""}:{f if f != "None" else ""}]")
                        else:
                            stack.append(f"{b}.{a})")
                    else:
                        stack.append(f"getattr({b}, {a})")
                    continue
                stack.append(f"{b}{name}{a}")

            # compare_op is also binary but it thankfully has fewer edge cases than BINARY_OP
            case "COMPARE_OP":
                a = stack.pop()
                b = stack.pop()
                nmatch = re.search(r"bool\((.+)", name)
                stack.append(f"{b}{nmatch.group(1)}{a}")

            # numbers
            case "LOAD_SMALL_INT":
                stack.append(idx)

            # this isn't relevant to us
            case "RESUME":
                pass

            # this one is weird and i don't fully get the nuances of it
            case "RETURN_VALUE":
                # if we're in a ternary, this means we've finally evaluated all 3 parts
                if ternaryState >= 1:
                    a = stack.pop()
                    b = stack.pop()
                    c = stack.pop()
                    if needs_parentheses(a):
                        a = f"({a})"
                    if needs_parentheses(b):
                        b = f"({b})"
                    stack.append(f"({a} if {c} else {b})")
                    ternaryState -= 1
                    if ternaryState == 0:
                        if retMode:
                            return stack.pop()
                        break
                # this (and right above it) are where retMode are relevant
                if retMode:
                    return stack.pop()
                
            # this is handled in MAKE_FUNCTION (different python versions switch between this and an argument in MAKE_FUNCTION)
            case "SET_FUNCTION_ATTRIBUTE":
                pass

            # ternary operator
            case "POP_JUMP_IF_FALSE":
                cond = stack.pop()

                # evaluate the else block
                # find the label to jump to
                toLoc = re.search(r"to ([0-9a-zA-Z_]+)", name)
                if toLoc == None:
                    print("POP_JUMP_IF_FALSE issue:", idx, name)
                    continue
                toLoc = toLoc.group(1)

                # assuming toLoc is a label
                jump = re.search(rf"{toLoc}:(.+)", func, re.MULTILINE | re.DOTALL)
                if jump == None:
                    print("POP_JUMP_IF_FALSE jump issue:", idx, name)
                    continue

                elseBlock = parse_bytecode(jump.group(1), variables, cobj, closure, True)

                stack.append(cond)
                stack.append(elseBlock)
            case "NOT_TAKEN":
                ternaryState += 1
            # unknown bytecode instruction
            case x:
                print(x, idx, name)
                print(line)
                x += "i"
                
    return f"lambda {variables[0] if 0 in variables else "_"}: {stack[len(stack) - 1]}"

if __name__ == "__main__":
    one = lambda a: a
    succ = lambda n: lambda a: lambda b: a(n(a)(b))
    print(lambda_to_string(succ(succ(one))))

    # handles any partial application
    print(lambda_to_string(succ(one)(lambda x: x+1)))

    # this is how to evaluate the above
    print(succ(one)(lambda x: x+1)(0))