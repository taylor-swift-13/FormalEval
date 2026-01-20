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
    (map ascii_of_nat
         [100; 109; 70; 87; 104; 72; 119; 100; 114; 110; 101; 110; 101; 119; 105; 84; 104; 104; 105; 115; 110; 101; 115; 119; 108; 119; 105; 110; 101; 115])
    313.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.