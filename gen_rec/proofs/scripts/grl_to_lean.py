import sys
import re

def tokenize(s):
    token_pattern = re.compile(r'M|C|R|Z\d+|S|P|\(|\)|,|\d+')
    return token_pattern.findall(s)

class Parser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def consume(self, expected=None):
        tok = self.peek()
        if expected is not None and tok != expected:
            raise ValueError(f"Expected {expected}, got {tok} at pos {self.pos}")
        self.pos += 1
        return tok

    def parse_expr(self):
        tok = self.consume()
        if tok == 'M':
            self.consume('(')
            expr = self.parse_expr()
            self.consume(')')
            return ('M', expr)
        elif tok == 'C':
            self.consume('(')
            h = self.parse_expr()
            self.consume(',')
            gs = []
            while True:
                gs.append(self.parse_expr())
                if self.peek() == ',':
                    self.consume(',')
                else:
                    break
            self.consume(')')
            return ('C', h, gs)
        elif tok == 'R':
            self.consume('(')
            g = self.parse_expr()
            self.consume(',')
            h = self.parse_expr()
            self.consume(')')
            return ('R', g, h)
        elif tok.startswith('Z'):
            k = int(tok[1:])
            return ('Z', k)
        elif tok == 'S':
            return ('S',)
        elif tok == 'P':
            self.consume('(')
            k = int(self.consume())
            self.consume(',')
            i = int(self.consume())
            self.consume(')')
            return ('P', k, i)
        else:
            raise ValueError(f"Unexpected token {tok}")

def to_lean(ast):
    if ast[0] == 'M':
        # Usually we only care about the inner function of M for PRF holdouts
        return to_lean(ast[1])
    elif ast[0] == 'C':
        h = to_lean(ast[1])
        gs = ", ".join(to_lean(g) for g in ast[2])
        return f"PRF.comp ({h}) prf_list![{gs}]"
    elif ast[0] == 'R':
        g = to_lean(ast[1])
        h = to_lean(ast[2])
        return f"PRF.primRec ({g}) ({h})"
    elif ast[0] == 'Z':
        return f"PRF.zero {ast[1]}"
    elif ast[0] == 'S':
        return f"PRF.succ"
    elif ast[0] == 'P':
        k = ast[1]
        i = ast[2] - 1
        return f"(PRF.proj {k} ⟨{i}, by decide⟩)"

def process_file(input_path, output_path, module_name):
    holdouts = []
    with open(input_path, 'r') as f:
        for line in f:
            line = line.strip()
            if line.startswith("grf="):
                # Extract the expression part
                expr_part = line.split(" ")[0][4:]
                tokens = tokenize(expr_part)
                parser = Parser(tokens)
                ast = parser.parse_expr()
                holdouts.append((expr_part, ast))

    with open(output_path, 'w') as out:
        out.write(f"import GenRec.Syntax\n")
        out.write(f"import GenRec.Semantics\n\n")
        out.write(f"open GenRec\n\n")
        out.write(f"namespace {module_name}\n\n")
        
        for idx, (expr_part, ast) in enumerate(holdouts):
            lean_code = to_lean(ast)
            # Find the arity of the PRF (which is the inner function of M)
            # The arity should be 1 because M(f) has arity k if f has arity k+1, and these are arity 0 holdouts.
            # So the PRF is arity 1.
            out.write(f"-- Translating holdout {idx}\n")
            out.write(f"-- {expr_part}\n")
            out.write(f"def holdout_{idx} : PRF 1 :=\n")
            out.write(f"  {lean_code}\n\n")
            
            out.write(f"theorem holdout_{idx}_diverges : ∀ x, evalPRF holdout_{idx} (fun _ => x) > 0 := by\n")
            out.write(f"  sorry\n\n")
            
        out.write(f"end {module_name}\n")

if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("Usage: python grl_to_lean.py <input.grl> <output.lean> <ModuleName>")
        sys.exit(1)
    process_file(sys.argv[1], sys.argv[2], sys.argv[3])
