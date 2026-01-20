Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Fixpoint total_chars (l : list string) : nat :=
  match l with
  | [] => 0
  | h :: t => String.length h + total_chars t
  end.

Definition total_match_spec (lst1 lst2 output : list string) : Prop :=
  (total_chars lst1 <= total_chars lst2 /\ output = lst1) \/
  (total_chars lst1 > total_chars lst2 /\ output = lst2).

Open Scope string_scope.

Example total_match_test :
  total_match_spec ["hijklmnop"; "qrsworldtuv"; "qrsworldtuv"] ["hijklmnop"; "qrsworldtuv"; "qrsworldtuv"] ["hijklmnop"; "qrsworldtuv"; "qrsworldtuv"].
Proof.
  unfold total_match_spec.
  left.
  split.
  - simpl. reflexivity.
  - reflexivity.
Qed.