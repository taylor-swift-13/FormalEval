Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition how_many_times_spec (s : string) (sub : string) (res : nat) : Prop :=
  res = List.length (List.filter (fun i => String.eqb (substring i (String.length sub) s) sub) (seq 0 (String.length s))).

Example test_case_long_strings: how_many_times_spec "bLorem ipsum dolor sit amet, consetctetur adipiscing elit.a" "bThe quick brown fox jumps over the lazycacccccacipsum dog.a" 0.
Proof.
  unfold how_many_times_spec.
  compute.
  reflexivity.
Qed.