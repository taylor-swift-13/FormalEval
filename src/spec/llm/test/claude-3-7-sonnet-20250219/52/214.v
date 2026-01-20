Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => Z.ltb x t) l.

Example test_below_threshold :
  below_threshold_spec [100%Z; 200%Z; 300%Z; 0%Z; 0%Z; 0%Z; 0%Z] (-1%Z) false.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.