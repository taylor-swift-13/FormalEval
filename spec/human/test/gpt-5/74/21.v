Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.

Import ListNotations.
Open Scope string_scope.

Definition problem_74_pre (lst1 lst2 : list string) : Prop := True.

Definition problem_74_spec (lst1 lst2 output : list string) : Prop :=
  let sum := fun l => fold_left (fun acc s => acc + String.length s) l 0 in
  (sum lst1 <= sum lst2 /\ output = lst1) \/
  (sum lst1 > sum lst2 /\ output = lst2).

Example problem_74_example_coding_is_fun_coding_coding_is_awesome :
  problem_74_spec ["coding"; "is"; "fun"; "coding"] ["coding"; "is"; "awesome"] ["coding"; "is"; "awesome"].
Proof.
  unfold problem_74_spec.
  simpl.
  right.
  split; [lia | reflexivity].
Qed.