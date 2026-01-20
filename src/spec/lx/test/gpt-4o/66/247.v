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
      [97; 97; 97; 97; 97; 98; 98; 98; 98; 98; 98; 99; 99; 99; 99; 99; 99;
       100; 100; 75; 100; 101; 101; 101; 102; 102; 102; 103; 103; 103; 103;
       72; 72; 72; 72; 72; 73; 73; 73; 73; 74; 74; 74; 74; 75; 75; 75; 75;
       76; 76; 76; 76; 77; 77; 77; 77; 78; 78; 78; 78; 79; 79; 79; 79; 80;
       80; 80; 81; 81; 81; 81; 86; 86; 86; 87; 87; 87; 88; 88; 88; 89; 89;
       89; 90; 90; 90])
    4447.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.