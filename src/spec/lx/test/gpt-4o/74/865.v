Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

Fixpoint total_chars (l : list string) : nat :=
  match l with
  | [] => 0
  | h :: t => String.length h + total_chars t
  end.

Definition total_match_spec (lst1 lst2 output : list string) : Prop :=
  (total_chars lst1 <= total_chars lst2 /\ output = lst1) \/
  (total_chars lst1 > total_chars lst2 /\ output = lst2).

Example total_match_test_case :
  total_match_spec ["HELLO"; "WORLD"; "HOW"; "OyoUU"; "Ohi"; "WORLD"; "HOW"]
                   ["HELLO"; "WORLD"; "HOW"; "OyoUU"; "Ohi"; "WORLD"; "HOW"]
                   ["HELLO"; "WORLD"; "HOW"; "OyoUU"; "Ohi"; "WORLD"; "HOW"].
Proof.
  unfold total_match_spec.
  left.
  split.
  - simpl. reflexivity.
  - reflexivity.
Qed.