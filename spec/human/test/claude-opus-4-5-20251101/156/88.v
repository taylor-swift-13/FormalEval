Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.

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

Example test_31 : problem_156_spec 31 "xxxi".
Proof.
  unfold problem_156_spec.
  split.
  - split; lia.
  - exists 0, 0, 3, 1.
    exists [], [], ["x"%char; "x"%char; "x"%char], ["i"%char].
    split. { reflexivity. }
    split. { reflexivity. }
    split. { reflexivity. }
    split. { reflexivity. }
    split. { reflexivity. }
    split. { right. split; reflexivity. }
    split. { unfold roman_digit_spec. left. split; reflexivity. }
    split. { 
      unfold roman_digit_spec.
      right. right. right. left.
      split; reflexivity.
    }
    split. { 
      unfold roman_digit_spec.
      right. left.
      split; reflexivity.
    }
    reflexivity.
Qed.