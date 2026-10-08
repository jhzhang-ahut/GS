from collections import defaultdict


class Monomial:
    def __init__(self, letters):
        self.letters = tuple(letters)

    def __mul__(self, other):
        return Monomial(self.letters + other.letters)

    def __len__(self):
        return len(self.letters)

    def __eq__(self, other):
        return self.letters == other.letters

    def __hash__(self):
        return hash(self.letters)

    def __str__(self):
        return ''.join(self.letters)

    def reversed(self):
        return Monomial(list(reversed(self.letters)))

    def __repr__(self):
        return f"Monomial({self.letters})"

    def is_prefix(self, other):
        if len(self) > len(other):
            return False
        return other.letters[:len(self)] == self.letters

    def is_suffix(self, other):
        if len(self) > len(other):
            return False
        return other.letters[-len(self):] == self.letters


class Polynomial:
    def __init__(self, terms=None):
        self.terms = defaultdict(int)
        if terms:
            for mono, coeff in terms.items():
                self.terms[mono] += coeff
            self.terms = {m: c for m, c in self.terms.items() if c != 0}

    def leading_monomial(self, order):
        if not self.terms:
            return None
        return max(self.terms.keys(), key=lambda m: order(m))

    def leading_coefficient(self, order):
        lm = self.leading_monomial(order)
        return self.terms[lm] if lm else 0

    def __sub__(self, other):
        new_terms = defaultdict(int)
        for mono, coeff in self.terms.items():
            new_terms[mono] += coeff
        for mono, coeff in other.terms.items():
            new_terms[mono] -= coeff
        return Polynomial(new_terms)

    def __mul__(self, scalar):
        if scalar == 0:
            return Polynomial()

        new_terms = {}
        for mono, coeff in self.terms.items():
            new_terms[mono] = coeff * scalar
        return Polynomial(new_terms)

    def __rmul__(self, scalar):
        return self.__mul__(scalar)

    def right_multiply_monomial(self, mono):
        new_terms = {}
        for m, c in self.terms.items():
            new_terms[m * mono] = c
        return Polynomial(new_terms)

    def left_multiply_monomial(self, mono):
        new_terms = {}
        for m, c in self.terms.items():
            new_terms[mono * m] = c
        return Polynomial(new_terms)

    def reverse_monomials(self):
        new_terms = {mono.reversed(): coeff for mono, coeff in self.terms.items()}
        return Polynomial(new_terms)

    def is_zero(self):
        return len(self.terms) == 0

    def __str__(self):
        terms = []
        for mono, coeff in self.terms.items():
            if coeff == 1:
                terms.append(f"{mono}")
            elif coeff == -1:
                terms.append(f"-{mono}")
            else:
                terms.append(f"{coeff}*{mono}")
        if not terms:
            return "0"
        first = terms[0]
        if len(terms) > 1 and first.startswith('-'):
            result = f"-{first[1:]}"
        else:
            result = first
        for term in terms[1:]:
            if term.startswith('-'):
                result += f" - {term[1:]}"
            else:
                result += f" + {term}"
        return result

    def __repr__(self):
        return f"Polynomial({dict(self.terms)})"


def composition(f, g, order):
    f = (f.leading_coefficient(order)) * f
    g = (g.leading_coefficient(order)) * g
    a = f.leading_monomial(order)
    b = g.leading_monomial(order)

    if a is None or b is None:
        return None

    for k in range((min(len(a), len(b))), 0, -1):
        prefix = Monomial(b.letters[:k])
        suffix = Monomial(a.letters[-k:])
        if prefix == suffix:
            comp = f.right_multiply_monomial(Monomial(b.letters[k:])) - g.left_multiply_monomial(
                Monomial(a.letters[:-k]))
            return comp

    b_len = len(b)
    a_len = len(a)
    if b_len > a_len:
        return None
    for j in range(0, a_len - b_len + 1):
        i = j + b_len
        if a.letters[j:i] == b.letters:
            u = Monomial(a.letters[:j])
            v = Monomial(a.letters[i:])
            comp = f - g.left_multiply_monomial(u).right_multiply_monomial(v)
            return comp

    return None


def reduce_polynomial(p, basis, order):
    while True:
        reduced = False
        for f in basis:
            lm_f = f.leading_monomial(order)
            if lm_f is None:
                continue

            for m in list(p.terms.keys()):
                lm_f_len = len(lm_f)
                m_len = len(m)
                if m_len < lm_f_len:
                    continue
                for i in range(0, m_len - lm_f_len + 1):
                    sub_mono = Monomial(m.letters[i:i + lm_f_len])
                    if sub_mono == lm_f:
                        u = Monomial(m.letters[:i])
                        v = Monomial(m.letters[i + lm_f_len:])
                        coeff = p.terms[m] / f.leading_coefficient(order)

                        reduction = f.left_multiply_monomial(u).right_multiply_monomial(v)
                        scaled_terms = {m: c * coeff for m, c in reduction.terms.items()}
                        scaled_reduction = Polynomial(scaled_terms)

                        p = p - scaled_reduction
                        reduced = True
                        break
                if reduced:
                    break
            if reduced:
                break
        if not reduced:
            break
    if p.leading_coefficient(order)==0:
       return p
    else:
        return p*(1/p.leading_coefficient(order))

def local_grobner_shirshov_basis(generators, f, order):
    reduced_f = f
    basis = generators.copy()

    queue = [(f_basis, g_basis) for f_basis in basis for g_basis in basis if f_basis != g_basis]
    testnumber = 1

    while queue:
        f_queue, g_queue = queue.pop(0)
        comp = composition(f_queue, g_queue, order)

        if comp is None:
            continue

        reduced_comp = reduce_polynomial(comp, basis, order)

        if not reduced_comp.is_zero():
            basis.append(reduced_comp)
            for h in basis:
                if h != reduced_comp:
                    queue.append((reduced_comp, h))
                    queue.append((h, reduced_comp))

        reduced_f = reduce_polynomial(reduced_f, basis, order)
        if reduced_f.is_zero():
            print(True)
            testnumber = 0
            break

    if testnumber == 1:
        print(False)
    return basis


def grobner_shirshov_basis(generators, order):
    basis = generators.copy()
    queue = [(f, g) for f in basis for g in basis if f != g]

    while queue:
        f, g = queue.pop(0)
        comp = composition(f, g, order)

        if comp is None:
            continue

        reduced_comp = reduce_polynomial(comp, basis, order)

        if not reduced_comp.is_zero():
            basis.append(reduced_comp)
            for h in basis:
                if h != reduced_comp:
                    queue.append((reduced_comp, h))
                    queue.append((h, reduced_comp))

    return basis


def deg_lex_order(monomial):
    def get_priority(letter):
        if letter.isupper():
            return 26 + ord(letter) - ord('A')
        else:
            return (ord(letter) - ord('a'))

    priority_sequence = [get_priority(c) for c in monomial.letters]
    return (len(monomial), priority_sequence)


if __name__ == "__main__":
    a = Monomial(['a'])
    b = Monomial(['b'])
    c = Monomial(['c'])
    y = Monomial(['y'])
    s = Monomial(['s'])
    t = Monomial(['t'])

    f1 = Polynomial({b * s * y: 1, y: -1})
    f2 = Polynomial({y * t * c: 1, y: -1})
    f3 = Polynomial({y * a * b: 1, b: -1})
    f4 = Polynomial({c * a * y: 1, c: -1})

    def lex_order(monomial):
        return monomial.letters

    basis = grobner_shirshov_basis([f1, f2, f3, f4], deg_lex_order)
    print("Grobner-Shirshov basis:")
    for poly in basis:
        print(poly)