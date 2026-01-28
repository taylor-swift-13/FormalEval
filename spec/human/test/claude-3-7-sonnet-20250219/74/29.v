Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope string_scope.

Definition problem_74_pre (lst1 lst2 : list string) : Prop := True.

Definition problem_74_spec (lst1 lst2 output : list string) : Prop :=
  let sum := fun l => fold_left (fun acc s => acc + String.length s) l 0 in
  (sum lst1 <= sum lst2 /\ output = lst1) \/
  (sum lst1 > sum lst2 /\ output = lst2).

Example test_total_match_hello_world:
  problem_74_spec ["hello"; "world"] ["cathi"; "there"] ["hello"; "world"].
Proof.
  unfold problem_74_spec.
  simpl.
  left.
  split.
  - simpl.
    (* length "hello" = 5, length "world" = 5, sum lst1 = 10 *)
    (* length "cathi" = 5, length "there" = 5, sum lst2 = 10 *)
    reflexivity.
  - reflexivity.
Qed.