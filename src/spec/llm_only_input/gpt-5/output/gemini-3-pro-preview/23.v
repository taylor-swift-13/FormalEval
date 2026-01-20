Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Example strlen_spec_test_case :
  let input := [""] in
  exists res, strlen_spec (hd "" input) res /\ Z.of_nat res = 0%Z.
Proof.
  simpl.
  exists 0%nat.
  split.
  - unfold strlen_spec. simpl. reflexivity.
  - simpl. reflexivity.
Qed.