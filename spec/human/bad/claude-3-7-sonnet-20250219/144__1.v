Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition char_to_digit (c : ascii) : nat :=
  let n := nat_of_ascii c in
  let zero := nat_of_ascii ("0"%char) in
  n - zero.

Inductive list_ascii_to_nat_rel : list ascii -> nat -> Prop :=
| latn_nil : list_ascii_to_nat_rel [] 0
| latn_cons : forall c l n,
    list_ascii_to_nat_rel l n ->
    list_ascii_to_nat_rel (l ++ [c]) (n * 10 + char_to_digit c).

Definition Parse_Fraction (s : list ascii) (num den : nat) : Prop :=
  exists num_s den_s : list ascii,
    s = num_s ++ ["/"%char] ++ den_s /\
    list_ascii_to_nat_rel num_s num /\
    list_ascii_to_nat_rel den_s den.

Definition problem_144_spec (x n : string) (output : bool) : Prop :=
  exists num_x den_x num_n den_n : nat,
    Parse_Fraction (list_ascii_of_string x) num_x den_x /\
    Parse_Fraction (list_ascii_of_string n) num_n den_n /\
    num_x > 0 /\ den_x > 0 /\
    num_n > 0 /\ den_n > 0 /\
    let product_num := num_x * num_n in
    let product_den := den_x * den_n in
    output = if Nat.eqb (Nat.modulo product_num product_den) 0 then true else false.

(* Helper lemmas prove char_to_digit results *)
Lemma char_to_digit_0 : char_to_digit "0"%char = 0.
Proof. reflexivity. Qed.

Lemma char_to_digit_1 : char_to_digit "1"%char = 1.
Proof. reflexivity. Qed.

Lemma char_to_digit_2 : char_to_digit "2"%char = 2.
Proof. reflexivity. Qed.

Lemma char_to_digit_5 : char_to_digit "5"%char = 5.
Proof. reflexivity. Qed.

Lemma char_to_digit_6 : char_to_digit "6"%char = 6.
Proof. reflexivity. Qed.

Lemma char_to_digit_7 : char_to_digit "7"%char = 7.
Proof. reflexivity. Qed.

(* Prove specific list -> nat conversions *)
Lemma list_ascii_to_nat_rel_1 : list_ascii_to_nat_rel ["1"%char] 1.
Proof.
  change ["1"%char] with ([] ++ ["1"%char]).
  apply latn_cons. apply latn_nil.
Qed.

Lemma list_ascii_to_nat_rel_2 : list_ascii_to_nat_rel ["2"%char] 2.
Proof.
  change ["2"%char] with ([] ++ ["2"%char]).
  apply latn_cons. apply latn_nil.
Qed.

Lemma list_ascii_to_nat_rel_5 : list_ascii_to_nat_rel ["5"%char] 5.
Proof.
  change ["5"%char] with ([] ++ ["5"%char]).
  apply latn_cons. apply latn_nil.
Qed.

Lemma list_ascii_to_nat_rel_6 : list_ascii_to_nat_rel ["6"%char] 6.
Proof.
  change ["6"%char] with ([] ++ ["6"%char]).
  apply latn_cons. apply latn_nil.
Qed.

Lemma list_ascii_to_nat_rel_7 : list_ascii_to_nat_rel ["7"%char] 7.
Proof.
  change ["7"%char] with ([] ++ ["7"%char]).
  apply latn_cons. apply latn_nil.
Qed.

Lemma list_ascii_to_nat_rel_10 : list_ascii_to_nat_rel ["1"%char; "0"%char] 10.
Proof.
  change ["1"%char; "0"%char] with (([] ++ ["1"%char]) ++ ["0"%char]).
  apply latn_cons.
  apply list_ascii_to_nat_rel_1.
Qed.

Example simplify_1_5_5_1 :
  problem_144_spec "1/5" "5/1" true.
Proof.
  exists 1, 5, 5, 1.
  split.
  - unfold Parse_Fraction.
    exists ["1"%char], ["5"%char].
    split; [reflexivity|split].
    + apply list_ascii_to_nat_rel_1.
    + apply list_ascii_to_nat_rel_5.
  - split.
    + unfold Parse_Fraction.
      exists ["5"%char], ["1"%char].
      split; [reflexivity|split].
      * apply list_ascii_to_nat_rel_5.
      * apply list_ascii_to_nat_rel_1.
    + repeat split; lia.
Qed.

Qed.