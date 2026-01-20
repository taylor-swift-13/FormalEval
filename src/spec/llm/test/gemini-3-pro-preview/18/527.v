Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition how_many_times_spec (s : string) (sub : string) (res : nat) : Prop :=
  res = List.length (List.filter (fun i => String.eqb (substring i (String.length sub) s) sub) (seq 0 (String.length s))).

Example test_case_complex: how_many_times_spec "bThe quick brown fox jumps over the lazycaccoveamt,cccacipsum dog.a" "bThe quick brown fox jumps over the lazycaccoveamt,cccacipsum dog.a" 1.
Proof.
  unfold how_many_times_spec.
  vm_compute.
  reflexivity.
Qed.