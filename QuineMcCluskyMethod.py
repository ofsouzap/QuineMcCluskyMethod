from typing import Tuple, List, Union, Optional;
import copy;

TruthTable = List[Optional[bool]];
Minterm = List[bool];
Implicant = List[Optional[bool]];

def parse_opt_bool(s: str) -> Optional[bool]:
    s = s.strip().upper();
    if s == "1":
        return True;
    elif s == "0":
        return False;
    elif s == "X":
        return None;
    else:
        raise Exception("Invalid input string");

def pp_bool(b: bool):
    return "1" if b else "0";

def get_nth_bit(x: int, n: int) -> bool:
    return ((x >> n) & 1) != 0;

def implicant_to_minterm(implicant: Implicant) -> Minterm:

    out: Minterm = [];

    for v in implicant:
        if v == None:
            raise Exception("Can't convert Implicant with None value to Minterm.");
        else:
            out.append(v);

    return out;

def check_implicant_compatibility(a: Implicant, b: Implicant) -> bool:

    assert len(a) == len(b);

    diff_found = False;

    for i in range(len(a)):

        a_i = a[i];
        b_i = b[i];

        if (a_i == None) != (b_i == None):
            return False;
        elif (a_i != b_i):
            if diff_found:
                return False;
            else:
                diff_found = True;

    return True;

def get_implicant_set_count(imp: Implicant) -> int:

    set_count = 0;

    for v in imp:
        if v == True:
            set_count += 1;

    return set_count;

def merge_implicants(imp1: Implicant, imp2: Implicant) -> Implicant:

    assert len(imp1) == len(imp2);

    new: Implicant = [None for _ in range(len(imp1))];

    for i in range(len(imp1)):

        v1 = imp1[i];
        v2 = imp2[i];

        if v1 == v2:
            new[i] = v1;
        else:
            new[i] = None;

    return new;

def perform_implicant_merging(implicants: List[Implicant]) -> Tuple[List[Implicant], List[int]]:

    """Merges implicants where possible and identifies implicants unused in this process.

Returns:
    (next_implicants, unused_implicants)
    next_implicants - the next set of implicants that have been merged
    unused_implicants - indexes of implicants from the original set that haven't been used in creating next_implicants and so are prime implicants"""

    new_implicants: List[Implicant] = [];
    implicant_useds: List[bool] = [False for _ in range(len(implicants))];

    # Find mergeable implicants, merge them and record merged implicants

    imp_set_counts = [get_implicant_set_count(imp) for imp in implicants];

    for i in range(len(implicants)):
        imp1 = implicants[i];

        for j in range(len(implicants)):
            imp2 = implicants[j];

            if i == j:
                continue;

            elif imp_set_counts[i] != imp_set_counts[j] - 1:
                continue;

            else:
                if check_implicant_compatibility(imp1, imp2):

                    # Merge and add
                    new_implicants.append(merge_implicants(imp1, imp2));

                    # Mark as used
                    implicant_useds[i] = True;
                    implicant_useds[j] = True;

    # Get indexes of unused implicants to return

    unused_implicants: List[int] = [];

    for i in range(len(implicant_useds)):
        if not implicant_useds[i]:
            unused_implicants.append(i);

    # Return outputs

    return new_implicants, unused_implicants;

    pass; #TODO

def truth_table_index_to_implicant(bn: int, index: int) -> Implicant:

    implicant: Implicant = [];
    x = int(index);

    for _ in range(bn):
        implicant.insert(0, (x & 1) != 0);
        x >>= 1;

    return implicant;

def process_truth_table(bn: int, truth_table: TruthTable) -> Tuple[List[Implicant], List[Minterm]]:

    """Takes a truth table and returns the initial implicants to use and its required minterms."""

    implicants: List[Implicant] = [];
    minterms: List[Minterm] = [];

    for i in range(len(truth_table)):

        implicant = truth_table_index_to_implicant(bn, i);

        if truth_table[i] != False:
            implicants.append(implicant);

        if truth_table[i] == True:
            minterms.append(implicant_to_minterm(implicant));

    return implicants, minterms;

def get_prime_implicants(initial_implicants: List[Implicant]) -> List[Implicant]:

    implicants = copy.copy(initial_implicants);
    prime_implicants: List[Implicant] = [];

    while True:

        next_implicants, prime_implicant_indexes = perform_implicant_merging(implicants);

        for i in prime_implicant_indexes:
            prime_implicants.append(implicants[i]);

        if len(next_implicants) == 0:
            break;

        implicants = next_implicants;

    return prime_implicants;

def check_implicant_minterm_match(implicant: Implicant, minterm: Minterm) -> bool:

    assert len(implicant) == len(minterm);

    for i in range(len(implicant)):

        v_i = implicant[i];
        v_m = minterm[i];

        if v_i == v_m:
            continue;
        elif v_i == None:
            continue;
        else:
            return False;

    return True;

def perform_prime_implicant_chart(prime_implicants: List[Implicant], minterms: List[Minterm]) -> Tuple[List[Implicant], List[Implicant], List[Minterm]]:

    """Finds and returns essential prime implicants, non-essential prime implicants and any minterms not implied by the essential prime implicants"""

    covered_minterms: List[bool] = [False for _ in range(len(minterms))];
    essential_prime_implicant_indexes: List[int] = [];

    # Perform calculations

    for minterm in minterms:

        imp_match_found = False;
        imp_match_index = -1;
        second_match_found = False;

        for imp_i in range(len(prime_implicants)):
            implicant = prime_implicants[imp_i];

            if check_implicant_minterm_match(implicant, minterm):
                if imp_match_found:
                    second_match_found = True;
                    break;
                else:
                    imp_match_found = True;
                    imp_match_index = imp_i;

        if imp_match_found and (not second_match_found): # Matched implicant is an essential prime implicant

            assert imp_match_index >= 0;

            essential_prime_implicant = prime_implicants[imp_match_index];

            # Store prime implicant as essential
            essential_prime_implicant_indexes.append(imp_match_index);

            # Set minterms that the prime implicant implies to covered
            for mt_i in range(len(minterms)):
                mt = minterms[mt_i];
                if check_implicant_minterm_match(essential_prime_implicant, mt):
                    covered_minterms[mt_i] = True;

    # Process results

    essential_prime_implicants: List[Implicant] = [];
    nonessential_prime_implicants: List[Implicant] = [];
    remaining_minterms: List[Minterm] = [];

    for i in range(len(prime_implicants)):
        if i in essential_prime_implicant_indexes:
            essential_prime_implicants.append(prime_implicants[i]);
        else:
            nonessential_prime_implicants.append(prime_implicants[i]);

    for mt_i in range(len(minterms)):
        if not covered_minterms[mt_i]:
            remaining_minterms.append(minterms[mt_i]);

    # Return outputs

    return essential_prime_implicants, nonessential_prime_implicants, remaining_minterms;

def check_implicants_cover_minterms(implicants: List[Implicant], minterms: List[Minterm]) -> bool:

    for minterm in minterms:
        if all(map(lambda imp: check_implicant_minterm_match(imp, minterm) == False, implicants)):
            return False;

    return True;

def calculate_used_prime_implicants_for_minterms(prime_implicants: List[Implicant], minterms: List[Minterm]) -> Optional[List[Implicant]]:

    #TODO: This is a very inefficient solution. Later on, should try to implement a better, more efficient solution

    min_imp_count: Optional[int] = None;
    min_imps: Optional[List[Implicant]] = None;

    for bs_n in range(2**len(prime_implicants)):

        # Identify used implicants for test

        use_imps = [get_nth_bit(bs_n, i) for i in range(len(prime_implicants))];

        used_imps: List[Implicant] = [];
        for i in range(len(use_imps)):
            if use_imps[i]:
                used_imps.append(prime_implicants[i]);

        if (min_imp_count != None) and (len(used_imps) >= min_imp_count):
            # Compare to current minimum before testing (to save time)
            continue;

        elif not check_implicants_cover_minterms(used_imps, minterms):
            # Check all minterms covered
            continue;

        else:
            # Set as current minimum otherwise
            min_imp_count = len(used_imps);
            min_imps = used_imps;

    return min_imps;

def implicant_to_str(imp: Implicant) -> str:
    return " ".join("1" if v == True else "-" if v == None else "0" for v in imp);

def main():

    # Get variable count input

    bn = int(input("Numbers of variables: ")); # Enter number of variables

    assert bn > 0;

    # Get truth table input

    truth_table: TruthTable = [];

    for i in range(0, 1 << bn):
        
        vs = [((i >> k) & 1) != 0 for k in range(bn-1, -1, -1)];
        
        vs_line = " ".join([pp_bool(v) for v in vs]);
        b = parse_opt_bool(input(f"{vs_line} = ")); # Enter 1 or 0

        truth_table.append(b);

    # Convert truth table

    initial_implicants: List[Implicant];
    req_minterms: List[Minterm];

    initial_implicants, req_minterms = process_truth_table(bn, truth_table);

    # Calculate prime implicants

    prime_implicants = get_prime_implicants(initial_implicants);

    # Perform prime implicant chart calculations

    essential_prime_implicants, nonessential_prime_implicants, remaining_minterms = perform_prime_implicant_chart(prime_implicants, req_minterms);

    # Record used prime implicants

    covering_set: List[Implicant] = [];

    for imp in essential_prime_implicants:
        covering_set.append(imp);

    # Select other included implicants

    used_nonessential_prime_implicants = calculate_used_prime_implicants_for_minterms(nonessential_prime_implicants, remaining_minterms);

    if used_nonessential_prime_implicants == None:
        raise Exception("No solution could be found for using non-essential prime implicants.");

    for imp in used_nonessential_prime_implicants:
        covering_set.append(imp);

    # Format and return output

    print("\n".join(implicant_to_str(imp) for imp in covering_set));

if __name__ == "__main__":
    main();
