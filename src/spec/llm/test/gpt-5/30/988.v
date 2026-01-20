Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition Rgtb (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgtb x 0%R) l.

Example get_positive_spec_test :
  get_positive_spec
    [-1.3426789806479305%R; 32.97170491287429%R; -2.25%R; 32.97170491287429%R]
    [32.97170491287429%R; 32.97170491287429%R].
Proof.
  unfold get_positive_spec.
  simpl.
  unfold Rgtb.
  destruct (Rgt_dec (-1.3426789806479305%R) 0%R) as [H1|H1].
  - assert (-1.3426789806479305%R <= 0%R) by lra.
    exfalso; lra.
  - simpl.
    unfold Rgtb.
    destruct (Rgt_dec 32.97170491287429%R 0%R) as [H2|H2].
    + simpl.
      unfold Rgtb.
      destruct (Rgt_dec (-2.25%R) 0%R) as [H3|H3].
      * assert (-2.25%R <= 0%R) by lra.
        exfalso; lra.
      * simpl.
        unfold Rgtb.
        destruct (Rgt_dec 32.97170491287429%R 0%R) as [H4|H4].
        -- simpl. reflexivity.
        -- exfalso. apply H4. lra.
    + exfalso. apply H2. lra.
Qed.