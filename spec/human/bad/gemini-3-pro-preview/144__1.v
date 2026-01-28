Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Define character to digit conversion *)
Definition char_to_digit (c : ascii) : nat :=
  let n := nat_of_ascii c in
  let zero := nat_of_ascii "0"%char in
  n - zero.

(* Relational definition for parsing a list of ascii digits to a natural number *)
Inductive list_ascii_to_nat_rel : list ascii -> nat -> Prop :=
| latn_nil : list_ascii_to_nat_rel [] 0
| latn_cons : forall c l n,
    list_ascii_to_nat_rel l n ->
    list_ascii_to_nat_rel (l ++ [c]) (n * 10 + char_to_digit c).

(* Parse a fraction string (as list ascii) into numerator and denominator *)
Definition Parse_Fraction (s : list ascii) (num den : nat) : Prop :=
  exists num_s den_s : list ascii,
    s = num_s ++ ["/"%char] ++ den_s /\
    list_ascii_to_nat_rel num_s num /\
    list_ascii_to_nat_rel den_s den.

(* Constraint definition *)
Definition problem_144_pre (x n : string) : Prop :=
  exists nx dx ny dy,
    Parse_Fraction (list_ascii_of_string x) nx dx /\
    Parse_Fraction (list_ascii_of_string n) ny dy /\
    nx > 0 /\ dx > 0 /\ ny > 0 /\ dy > 0.

(* Specification definition *)
Definition problem_144_spec (x n : string) (output : bool) : Prop :=
  exists num_x den_x num_n den_n : nat,
    Parse_Fraction (list_ascii_of_string x) num_x den_x /\
    Parse_Fraction (list_ascii_of_string n) num_n den_n /\
    num_x > 0 /\ den_x > 0 /\
    num_n > 0 /\ den_n > 0 /\
    let product_num := num_x * num_n in
    let product_den := den_x * den_n in
    output = (if (product_num mod product_den) =? 0 then true else false).

(* Helper lemmas for converting characters to digits *)
Lemma char_to_digit_1 : char_to_digit "1"%char = 1.
Proof. compute. reflexivity. Qed.

Lemma char_to_digit_5 : char_to_digit "5"%char = 5.
Proof. compute. reflexivity. Qed.

(* Helper tactic to prove list_ascii_to_nat_rel for single digit strings.
   It avoids using reflexivity on the relation itself, fixing the previous error. *)
Ltac prove_digit c val lemma_name :=
  change ([c]) with ([] ++ [c]);
  replace val with (0 * 10 + char_to_digit c) by (rewrite lemma_name; simpl; reflexivity);
  apply latn_cons;
  apply latn_nil.

(* The test case proof *)
Example test_case : problem_144_spec "1/5" "5/1" true.
Proof.
  unfold problem_144_spec.
  exists 1, 5, 5, 1.
  repeat split.

  (* 1. Prove Parse_Fraction for "1/5" *)
  - unfold Parse_Fraction.
    exists ["1"%char], ["5"%char].
    repeat split.
    + (* String concatenation check *)
      simpl. reflexivity.
    + (* Parse numerator "1" *)
      prove_digit "1"%char 1 char_to_digit_1.
    + (* Parse denominator "5" *)
      prove_digit "5"%char 5 char_to_digit_5.

  (* 2. Prove Parse_Fraction for "5/1" *)
  - unfold Parse_Fraction.
    exists ["5"%char], ["1"%char].
    repeat split.
    + (* String concatenation check *)
      simpl. reflexivity.
    + (* Parse numerator "5" *)
      prove_digit "5"%char 5 char_to_digit_5.
    + (* Parse denominator "1" *)
      prove_digit "1"%char 1 char_to_digit_1.

  (* 3. Prove numeric constraints *)
  - lia. (* 1 > 0 *)
  - lia. (* 5 > 0 *)
  - lia. (* 5 > 0 *)
  - lia. (* 1 > 0 *)

  (* 4. Prove the calculation result *)
  - simpl.
    (* (1 * 5) mod (5 * 1) = 5 mod 5 = 0 *)
    reflexivity.
Qed.