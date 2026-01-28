Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition how_many_times_spec (s : string) (sub : string) (res : nat) : Prop :=
  res = List.length (List.filter (fun i => String.eqb (substring i (String.length sub) s) sub) (seq 0 (String.length s))).

Example test_case_complex_strings: how_many_times_spec "conse ctedturThedotheobrownfg. quick brown foxamet, jumps over the lazy dog." "conse ctedturThedotheg. quick brown foxamet, juAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABmps over the lazy dog." 0.
Proof.
  unfold how_many_times_spec.
  reflexivity.
Qed.