Require Import List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => Z.ltb x t) l.

Example test_below_threshold :
  below_threshold_spec [6%Z; 5%Z; 5%Z; 6%Z; 7%Z; 7%Z] 300%Z true.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.