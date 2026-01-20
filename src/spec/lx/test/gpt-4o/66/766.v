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

Example digitSum_test_long_string :
  digitSum_spec
    (["t"; "t"; "a"; "b"; "s"; "t"; "t"; "e"; "s"; "t"; "s"; "I"; "s"; "a"; "C"; "r"; "a"; "z"; "y"; "M"; "i"; "E"; "R"; "S"; "B"; "C"; "D"; "E"; "F"; "G"; "H"; "I"; "J"; "K"; "L"; "M"; "N"; "O"; "P"; "Q"; "R"; "S"; "T"; "U"; "V"; "T"; "h"; "i"; "s"; "i"; "s"; "a"; "t"; "e"; "s"; "t"; "w"; "i"; "t"; "h"; "n"; "e"; "w"; "l"; "i"; "n"; "e"; "s"; "a"; "n"; "d"; "t"; "a"; "b"; "s"; "W"; "X"; "Y"; "A"; "T"; "h"; "i"; "s"; "Z"; "b"; "s"]%char)
    2634.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.