Require Import List.
Require Import String.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

Definition total_match_spec (lst1 lst2 : list string) (result : list string) : Prop :=
  let c1 := fold_left (fun acc s => acc + String.length s) lst1 0 in
  let c2 := fold_left (fun acc s => acc + String.length s) lst2 0 in
  (c1 <= c2 /\ result = lst1) \/ (c1 > c2 /\ result = lst2).

Example test_total_match_complex: total_match_spec 
  ["The"; "quick"; "brown"; "fox"; "jumps"; "over"; "the"; "lazy"; "dog"] 
  ["Lorem"; "ipsum"; "dolor"; "sit"; "amet"; "consectetur"; "adipiscing"; "elit"] 
  ["The"; "quick"; "brown"; "fox"; "jumps"; "over"; "the"; "lazy"; "dog"].
Proof.
  unfold total_match_spec.
  compute.
  left.
  split.
  - repeat constructor.
  - reflexivity.
Qed.