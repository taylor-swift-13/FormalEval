Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition how_many_times_spec (s : string) (sub : string) (res : nat) : Prop :=
  res = List.length (List.filter (fun i => String.eqb (substring i (String.length sub) s) sub) (seq 0 (String.length s))).

Example test_case_cac_longsub: how_many_times_spec "cac" "cafoipsuconsecteturmxc" 0.
Proof.
  unfold how_many_times_spec.
  simpl.
  reflexivity.
Qed.