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

Example digitSum_test_new :
  digitSum_spec
    [ascii_of_nat 72; ascii_of_nat 58; ascii_of_nat 59; ascii_of_nat 60; ascii_of_nat 58; ascii_of_nat 59; ascii_of_nat 60; ascii_of_nat 61; ascii_of_nat 62; ascii_of_nat 63; ascii_of_nat 64; ascii_of_nat 91; ascii_of_nat 92; ascii_of_nat 93; ascii_of_nat 94; ascii_of_nat 58; ascii_of_nat 95; ascii_of_nat 96; ascii_of_nat 123; ascii_of_nat 65; ascii_of_nat 66; ascii_of_nat 67; ascii_of_nat 49; ascii_of_nat 50; ascii_of_nat 51; ascii_of_nat 100; ascii_of_nat 101; ascii_of_nat 102; ascii_of_nat 61; ascii_of_nat 52; ascii_of_nat 53; ascii_of_nat 54; ascii_of_nat 71; ascii_of_nat 72; ascii_of_nat 73; ascii_of_nat 68; ascii_of_nat 32; ascii_of_nat 123; ascii_of_nat 124; ascii_of_nat 125; ascii_of_nat 126]
    554.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.