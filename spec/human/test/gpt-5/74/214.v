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

Example problem_74_example_equal_lists :
  problem_74_spec ["hello"; "world"; "hohw"; "are"; "you"; "hohw"]
                  ["hello"; "world"; "hohw"; "are"; "you"; "hohw"]
                  ["hello"; "world"; "hohw"; "are"; "you"; "hohw"].
Proof.
  unfold problem_74_spec.
  simpl.
  left.
  split; [lia | reflexivity].
Qed.