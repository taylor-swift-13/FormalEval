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

Example digitSum_test_stabsWXYAThisZa :
  digitSum_spec [ascii_of_nat 115; ascii_of_nat 116; ascii_of_nat 97; ascii_of_nat 98; ascii_of_nat 115; ascii_of_nat 87; ascii_of_nat 88; ascii_of_nat 89; ascii_of_nat 65; ascii_of_nat 84; ascii_of_nat 104; ascii_of_nat 105; ascii_of_nat 115; ascii_of_nat 90; ascii_of_nat 97] 503.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.