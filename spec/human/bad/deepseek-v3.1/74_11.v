Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.

Import ListNotations.

Definition problem_74_spec (lst1 lst2 output : list string) : Prop :=
  let sum := fun l => fold_left (fun acc s => acc + String.length s) l 0 in
  (sum lst1 <= sum lst2 /\ output = lst1) \/
  (sum lst1 > sum lst2 /\ output = lst2).

Example test_case_new : 
  problem_74_spec [["hello"; "world"]; ["hi"; "there"]] [["hello"; "world"]; ["hi"; "there"]] 
    [["hi"; "there"]].
Proof.
  unfold problem_74_spec.
  simpl.
  right.
  split.
  - simpl.
    lia.
  - reflexivity.
Qed.