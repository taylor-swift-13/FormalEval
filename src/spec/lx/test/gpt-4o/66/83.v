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
    (map ascii_of_nat [58;59;60;61;62;63;64;91;93;94;95;96;123;32;65;97;98;99;100;72;69;76;114;49;49;50;51;65;66;67;68;76;79;32;32;66;67;32;49;68;32;124;125;126])
    904.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.