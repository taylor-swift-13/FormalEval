Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Le.
Import ListNotations.
Open Scope nat_scope.

Definition roman_digit_spec (one ten five : ascii) (digit : nat) (res : list ascii) : Prop :=
  (digit = 0 /\ res = []) \/
  (digit = 1 /\ res = [one]) \/
  (digit = 2 /\ res = [one; one]) \/
  (digit = 3 /\ res = [one; one; one]) \/
  (digit = 4 /\ res = [one; five]) \/
  (digit = 5 /\ res = [five]) \/
  (digit = 6 /\ res = [five; one]) \/
  (digit = 7 /\ res = [five; one; one]) \/
  (digit = 8 /\ res = [five; one; one; one]) \/
  (digit = 9 /\ res = [one; ten]).

Definition problem_156_pre (number : nat) : Prop := 1 <= number /\ number <= 1000.

Definition problem_156_spec (number : nat) (result : string) : Prop :=
  1 <= number <= 1000 /\
  (exists m c x i rm rc rx ri,
    number = 1000 * m + 100 * c + 10 * x + i /\
    m = number / 1000 /\
    c = (number / 100) mod 10 /\
    x = (number / 10) mod 10 /\
    i = number mod 10 /\
    ( (m = 1 /\ rm = ["m"%char]) \/ (m = 0 /\ rm = []) ) /\
    roman_digit_spec "c"%char "m"%char "d"%char c rc /\
    roman_digit_spec "x"%char "c"%char "l"%char x rx /\
    roman_digit_spec "i"%char "x"%char "v"%char i ri /\
    result = string_of_list_ascii (rm ++ rc ++ rx ++ ri)).

Example example_19 : problem_156_spec 19 "xix".
Proof.
  unfold problem_156_spec.
  split.
  - apply le_n_S, le_0_n.
  - exists 0, 0, 1, 9, [], [], ["x"%char], ["i"%char; "x"%char].
    split; [ reflexivity | ].
    split; [ simpl; reflexivity | ].
    split; [ simpl; reflexivity | ].
    split; [ simpl; reflexivity | ].
    split; [ simpl; reflexivity | ].
    split.
    + left; split; reflexivity.
    + split.
      * left; split; reflexivity.
      * right; right; right; right; right; right; right; right; left; split; reflexivity.
    + simpl. reflexivity.
Qed.