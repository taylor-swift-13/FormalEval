Require Import List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => Z.ltb x t) l.

Example test_below_threshold : below_threshold_spec [1%Z; 3%Z; 7%Z; 11%Z] (-3)%Z false.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.