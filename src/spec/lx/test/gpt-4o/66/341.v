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
         [97; 97; 97; 97; 97; 98; 98; 98; 98; 98; 98; 99; 99; 99; 99; 99; 99; 100; 100; 100; 101; 101; 101; 102; 102; 102; 103; 103; 103; 103; 103; 72; 72; 72; 72; 72; 73; 73; 73; 73; 74; 74; 74; 74; 75; 105; 115; 75; 75; 75; 76; 76; 76; 76; 77; 77; 77; 77; 78; 78; 78; 78; 79; 79; 79; 79; 80; 80; 80; 81; 84; 84; 85; 85; 86; 86; 86; 84; 104; 33; 115; 33; 115; 36; 48; 110; 108; 121; 52; 116; 51; 115; 116; 33; 110; 103; 45; 49; 38; 50; 37; 51; 42; 52; 64; 53; 95; 99; 64; 53; 69; 83; 46; 52; 51; 48; 53; 116; 53; 110; 53; 116; 53; 118; 53; 102; 102; 53; 109; 109; 53; 103; 53; 53; 103; 110; 53; 116; 53; 84; 104; 53; 116; 53; 121; 110; 53; 116; 104; 121; 53; 104; 116; 53; 116; 53; 83; 53; 116; 53; 98; 115; 83; 80; 98; 112; 77; 53; 83; 84; 53; 84; 83; 53; 116; 53; 110; 53; 116; 53; 110; 53; 116; 53; 65; 114; 53; 116; 53; 112; 110; 53; 116; 53; 115; 104; 114; 53; 116; 53; 83; 83; 53; 116; 53; 118; 53; 116; 53; 115; 110; 53; 116; 53; 77; 53; 116; 53; 110; 89; 89; 89; 90; 90; 77; 90])
    5304.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.