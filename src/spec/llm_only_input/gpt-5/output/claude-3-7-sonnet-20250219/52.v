Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition below_threshold_spec (l : list nat) (t : nat) (res : bool) : Prop :=
  res = forallb (fun x => Nat.ltb x t) l.

Example below_threshold_spec_test :
  below_threshold_spec (map Z.to_nat [1%Z; 2%Z; 4%Z; 10%Z]) (Z.to_nat 100%Z) true.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.