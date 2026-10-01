import DMSolutions.OEIS_A211420.Solution

/-!
# Checks for the solution of `OeisA211420.conjecture1` to `OeisA211420.conjecture4`

* The definitions copied into `A211420Core` are the statement file's definitions (`rfl`).
* Each `conjectureN_solved` has exactly the type of the repository statement `conjectureN`.
* The solved theorems use only the standard axioms.
-/

-- The copied definitions agree with the statement file's definitions.
example : OeisA211420.a = A211420Core.a := rfl
example : OeisA211420.oddDescendingProduct = A211420Core.oddDescendingProduct := rfl

-- Each solved theorem has exactly the type of the repository statement.
example : type_of% @OeisA211420.conjecture1 = type_of% @OeisA211420.conjecture1_solved := rfl
example : type_of% @OeisA211420.conjecture2 = type_of% @OeisA211420.conjecture2_solved := rfl
example : type_of% @OeisA211420.conjecture3 = type_of% @OeisA211420.conjecture3_solved := rfl
example : type_of% @OeisA211420.conjecture4 = type_of% @OeisA211420.conjecture4_solved := rfl

-- The repository statements and ours, printed for comparison:
#check @OeisA211420.conjecture1
#check @OeisA211420.conjecture1_solved
#check @OeisA211420.conjecture2
#check @OeisA211420.conjecture2_solved
#check @OeisA211420.conjecture3
#check @OeisA211420.conjecture3_solved
#check @OeisA211420.conjecture4
#check @OeisA211420.conjecture4_solved

#print axioms OeisA211420.conjecture1_solved
#print axioms OeisA211420.conjecture2_solved
#print axioms OeisA211420.conjecture3_solved
#print axioms OeisA211420.conjecture4_solved
