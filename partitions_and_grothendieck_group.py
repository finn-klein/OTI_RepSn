def is_restricted(l, p):
    k = len(l)
    return all([(l[i] - l[i+1] < p) for i in range(k-1)]) and \
        ((p == 2 and l[-1] == 1) or (p != 2 and l[-1] < p-1))

def all_parts_coprime(l, p):
    return prod(l)%p != 0

def is_p_regular(l, p):
    parts = l
    if len(parts) == 0:
        return True
    count = {n: len([0 for part in parts if part == n]) for n in set(parts) if n != 0}
    return max(count.values()) < p

#T[:, [i for i in range(len(cycleTypes)) if all_parts_coprime(cycleTypes[i], p)]]

n = 11
p = 2
G = SymmetricGroup(n)
cycleTypes = [conjClass.representative().cycle_type() for conjClass in G.conjugacy_classes()]
T = G.character_table()
colIdx = [i for i in range(len(cycleTypes)) if all_parts_coprime(cycleTypes[i], p)]
rowIdx = [i for i in range(len(cycleTypes)) if is_p_regular(cycleTypes[i], p)]
T_sub = T[rowIdx, colIdx]

A = matrix(GF(p), T_sub).inverse().transpose()

def lookup(l):
    n = 14
    p = 2
    G = SymmetricGroup(n)
    cycleTypes = [conjClass.representative().cycle_type() for conjClass in G.conjugacy_classes()]
    T = G.character_table()
    colIdx = [i for i in range(len(cycleTypes)) if all_parts_coprime(cycleTypes[i], p)]
    rowIdx = [i for i in range(len(cycleTypes)) if is_p_regular(cycleTypes[i], p)]
    T_sub = T[rowIdx, colIdx]
    A = matrix(GF(p), T_sub).inverse().transpose()

    type_idx = cycleTypes.index(l)
    mults = A * matrix(GF(p), T[type_idx, colIdx]).transpose()
    # TODO: Generalise to account for multiplicities for arbitrary p
    nonzero_idcs = [rowIdx[i] for i in range(len(mults.columns()[0])) if mults.columns()[0][i] == 1]
    nonzero_partitions = [cycleTypes[i] for i in nonzero_idcs]
    return nonzero_partitions

def 

