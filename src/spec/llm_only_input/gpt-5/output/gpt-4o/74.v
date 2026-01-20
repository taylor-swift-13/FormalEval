Require Import List.
Require Import String.
Require Import Nat.
Require Import Lia.
Import ListNotations.

Definition total_match_spec (lst1 lst2 : list string) (result : list string) : Prop :=
  let c1 := fold_left (fun acc s => acc + String.length s) lst1 0 in
  let c2 := fold_left (fun acc s => acc + String.length s) lst2 0 in
  (c1 <= c2 /\ result = lst1) \/ (c1 > c2 /\ result = lst2).

Example total_match_spec_test_empty_empty :
  total_match_spec [] [] [].
Proof.
  unfold total_match_spec.
  simpl.
  left.
  split; [lia | reflexivity].
Qed.