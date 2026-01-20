Require Import Coq.Strings.Ascii Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition is_uppercase (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.leb 65 n) && (Nat.leb n 90).

Fixpoint sum_uppercase_ascii (l : list ascii) : nat :=
  match l with
  | [] => 0
  | c :: t =>
    if is_uppercase c
    then nat_of_ascii c + sum_uppercase_ascii t
    else sum_uppercase_ascii t
  end.

Definition digitSum_spec (l : list ascii) (n : nat) : Prop :=
  n = sum_uppercase_ascii l.

Example digitSum_test_case :
  digitSum_spec (map ascii_of_nat [84; 104; 33; 115; 33; 115; 36; 48; 110; 108; 121; 52; 116; 51; 115; 116; 33; 110; 103; 45; 102; 53; 109; 109; 53; 103; 53; 53; 103; 110; 53; 84; 116; 53; 84; 104; 53; 116; 53; 121; 110; 53; 116; 104; 121; 53; 104; 116; 53; 116; 36; 66; 99; 38; 68; 101; 102; 51; 64; 70; 53; 110]) 456.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.