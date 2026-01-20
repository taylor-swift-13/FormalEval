Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.BinNat.
Require Import Coq.micromega.Lia.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => Z.ltb x t) l.

Example test_below_threshold :
  below_threshold_spec [10000000%Z; 9000000%Z; 8000000%Z; 7000000%Z; 6000000%Z; 2000000%Z]
                       10000001%Z true.
Proof.
  unfold below_threshold_spec.
  simpl.
  repeat (rewrite forallb_cons).
  repeat (rewrite <- Bool.andb_true_iff).
  repeat split; lia.
Qed.