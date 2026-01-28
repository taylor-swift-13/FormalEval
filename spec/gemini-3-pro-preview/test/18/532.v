Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition how_many_times_spec (s : string) (sub : string) (res : nat) : Prop :=
  res = List.length (List.filter (fun i => String.eqb (substring i (String.length sub) s) sub) (seq 0 (String.length s))).

Example test_case_cquicfoxkacc_dog_r: how_many_times_spec "cquicfoxkacc" "dog.r" 0.
Proof.
  unfold how_many_times_spec.
  simpl.
  reflexivity.
Qed.