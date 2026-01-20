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
  digitSum_spec
    (map ascii_of_nat
         [116; 72; 105; 115; 73; 115; 97; 67; 114; 111; 97; 122; 121; 77; 105; 88; 111; 102; 85; 80; 80; 69; 82; 97; 110; 100; 108; 111; 87; 101; 114; 99; 97; 115; 101; 76; 69; 78; 84; 69; 82; 83])
    1401.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.