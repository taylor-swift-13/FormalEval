Require Import List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => Z.ltb x t) l.

Example test_below_threshold : below_threshold_spec [1%Z; 2%Z; -5%Z; -4%Z; 4%Z] 4%Z false.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.