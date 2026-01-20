Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition smallest_change_spec (arr : list Z) (res : nat) : Prop :=
  let half := Nat.div (length arr) 2 in
  let first := firstn half arr in
  let rfirst := firstn half (rev arr) in
  res = length (filter (fun p => negb (Z.eqb (fst p) (snd p))) (combine first rfirst)).

Example smallest_change_spec_test :
  smallest_change_spec [1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 42%Z; 17%Z; 1%Z; 42%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z] 5%nat.
Proof.
  unfold smallest_change_spec.
  vm_compute.
  reflexivity.
Qed.