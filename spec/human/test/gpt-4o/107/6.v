Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool Coq.ZArith.ZArith.
Import ListNotations.
Open Scope nat_scope.

(* Convert a natural number to a list of its digits in reverse *)
Fixpoint to_digits_helper (n k : nat) {struct k} : list nat :=
  match k with
  | 0 => []
  | S k' =>
    match n with
    | 0 => []
    | _ => (n mod 10) :: to_digits_helper (n / 10) k'
    end
  end.

Definition to_digits_rev (n : nat) : list nat :=
  to_digits_helper n n.

(* Check if two lists of natural numbers are equal *)
Fixpoint list_nat_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: t1, y :: t2 => andb (x =? y) (list_nat_eqb t1 t2)
  | _, _ => false
  end.

(* Check if a natural number is a palindrome *)
Definition is_palindrome_b (n : nat) : bool :=
  let d := to_digits_rev n in
  if (n =? 0) then false else list_nat_eqb d (rev d).

(* Check if a natural number is even *)
Definition is_even (n : nat) : bool :=
  (n mod 2 =? 0).

(* Check if a natural number is an even palindrome *)
Definition is_even_pal (n : nat) : bool :=
  andb (is_palindrome_b n) (is_even n).

(* Check if a natural number is an odd palindrome *)
Definition is_odd_pal (n : nat) : bool :=
  andb (is_palindrome_b n) (negb (is_even n)).

(* Count the number of elements in a range satisfying a predicate *)
Fixpoint count_in_range (P : nat -> bool) (k : nat) : nat :=
  match k with
  | 0 => 0
  | S k' =>
    (if P (S k') then 1 else 0) +
    count_in_range P k'
  end.

(* Implementation of counting palindromes *)
Definition count_palindromes_impl (n : nat) : nat * nat :=
  (count_in_range is_even_pal n, count_in_range is_odd_pal n).

(* Preconditions *)
Definition problem_107_pre (n : nat) : Prop := n > 0.

(* Specification *)
Definition problem_107_spec (n : nat) (output : nat * nat) : Prop :=
  output = count_palindromes_impl n.

(* Test case *)
Example test_case_19 :
  let input := 19%nat in
  let expected_output := (4, 6) in
  problem_107_pre input ->
  problem_107_spec input expected_output.
Proof.
  intros H.
  unfold problem_107_spec.
  unfold count_palindromes_impl.
  simpl.
  reflexivity.
Qed.