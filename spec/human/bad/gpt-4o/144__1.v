(* Import necessary Coq libraries *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* Convert a single ASCII character to a digit (0-9), assuming valid input *)
Definition char_to_digit (c : ascii) : nat :=
  let n := nat_of_ascii c in
  let zero := nat_of_ascii ("0"%char) in
  n - zero.

(* Helper relation: convert list ascii to natural number *)
Inductive list_ascii_to_nat_rel : list ascii -> nat -> Prop :=
| latn_nil : list_ascii_to_nat_rel [] 0
| latn_cons : forall c l n,
    list_ascii_to_nat_rel l n ->
    list_ascii_to_nat_rel (c :: l) (n * 10 + char_to_digit c).

(* Parse a fraction from a string in the form "numerator/denominator" *)
Definition Parse_Fraction (s : list ascii) (num den : nat) : Prop :=
  exists num_s den_s : list ascii,
    s = num_s ++ ["/"%char] ++ den_s /\
    list_ascii_to_nat_rel num_s num /\
    list_ascii_to_nat_rel den_s den.

(* Precondition for the problem: both x and n are valid fractions *)
Definition problem_144_pre (x n : string) : Prop :=
  exists nx dx ny dy,
    Parse_Fraction (list_ascii_of_string x) nx dx /\
    Parse_Fraction (list_ascii_of_string n) ny dy /\
    nx > 0 /\ dx > 0 /\ ny > 0 /\ dy > 0.

(* Specification for the problem: determine if the product is a whole number *)
Definition problem_144_spec (x n : string) (output : bool) : Prop :=
  exists num_x den_x num_n den_n : nat,
    Parse_Fraction (list_ascii_of_string x) num_x den_x /\
    Parse_Fraction (list_ascii_of_string n) num_n den_n /\
    num_x > 0 /\ den_x > 0 /\ num_n > 0 /\ den_n > 0 /\
    let product_num := num_x * num_n in
    let product_den := den_x * den_n in
    output = if (product_num mod product_den) =? 0
             then true
             else false.

(* Example proof for the given test case: simplify("1/5", "5/1") = True *)
Example test_simplify_1_5_5_1 :
  problem_144_spec "1/5" "5/1" true.
Proof.
  unfold problem_144_spec.
  exists 1, 5, 5, 1.
  split.
  - exists ["1"%char], ["5"%char]. split; [reflexivity|].
    split.
    + apply latn_cons with (c := "1"%char) (l := []); [apply latn_nil|].
      simpl. reflexivity.
    + apply latn_cons with (c := "5"%char) (l := []); [apply latn_nil|].
      simpl. reflexivity.
  - split.
    + exists ["5"%char], ["1"%char]. split; [reflexivity|].
      split.
      * apply latn_cons with (c := "5"%char) (l := []); [apply latn_nil|].
        simpl. reflexivity.
      * apply latn_cons with (c := "1"%char) (l := []); [apply latn_nil|].
        simpl. reflexivity.
    + repeat split; lia.
    + simpl. reflexivity.
Qed.