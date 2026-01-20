Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition how_many_times_spec (s : string) (sub : string) (res : nat) : Prop :=
  res = List.length (List.filter (fun i => String.eqb (substring i (String.length sub) s) sub) (seq 0 (String.length s))).

Example how_many_times_spec_test_empty_x :
  how_many_times_spec "" "x" 0%nat.
Proof.
  unfold how_many_times_spec.
  simpl.
  reflexivity.
Qed.

Example how_many_times_spec_test_empty_x_Z :
  exists res : nat, how_many_times_spec "" "x" res /\ Z.of_nat res = 0%Z.
Proof.
  exists 0%nat.
  split.
  - unfold how_many_times_spec. simpl. reflexivity.
  - simpl. reflexivity.
Qed.