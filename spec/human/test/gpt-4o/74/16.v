Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

Import ListNotations.
Open Scope string_scope.

Definition problem_74_pre (lst1 lst2 : list string) : Prop := True.

Definition problem_74_spec (lst1 lst2 output : list string) : Prop :=
  let sum := fun l => fold_left (fun acc s => acc + String.length s) l 0 in
  (sum lst1 <= sum lst2 /\ output = lst1) \/
  (sum lst1 > sum lst2 /\ output = lst2).

Example test_total_match_1 :
  problem_74_spec ["happy"; "birthday"; "sarah"] ["happy"; "birthday"; "sally"] ["happy"; "birthday"; "sarah"].
Proof.
  unfold problem_74_spec.
  simpl.
  left.
  split.
  - reflexivity.
  - reflexivity.
Qed.