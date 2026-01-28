Require Import List.
Require Import String.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

Definition total_match_spec (lst1 lst2 : list string) (result : list string) : Prop :=
  let c1 := fold_left (fun acc s => acc + String.length s) lst1 0 in
  let c2 := fold_left (fun acc s => acc + String.length s) lst2 0 in
  (c1 <= c2 /\ result = lst1) \/ (c1 > c2 /\ result = lst2).

Example test_total_match_1: total_match_spec ["hi"; "admin"; "admin"] ["how"; "are"; "yoU"] ["how"; "are"; "yoU"].
Proof.
  unfold total_match_spec.
  simpl.
  right.
  split.
  - repeat constructor.
  - reflexivity.
Qed.