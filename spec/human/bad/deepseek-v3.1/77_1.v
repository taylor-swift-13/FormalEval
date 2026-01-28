Require Import ZArith.
Open Scope Z_scope.

Definition iscube (a : Z) : bool :=
  match a with
  | 0 => true
  | _ =>
      let root := Z.sqrt (Z.abs a) in
      if Z.eqb (root * root * root) (Z.abs a) then true else false
  end.

Lemma iscube_correct : forall a, iscube a = true <-> (exists x : Z, a = x * x * x).
Proof.
  intros a. split.
  - intros H. unfold iscube in H.
    destruct a as [|p|p].
    + exists 0. reflexivity.
    + simpl in H.
      remember (Z.sqrt (Z.pos p)) as root.
      destruct (Z.eqb (root * root * root) (Z.pos p)) eqn:E.
      * exists root. apply Z.eqb_eq in E. assumption.
      * discriminate.
    + simpl in H.
      remember (Z.sqrt (Z.pos p)) as root.
      destruct (Z.eqb (root * root * root) (Z.pos p)) eqn:E.
      * exists (-root). 
        rewrite <- Z.opp_involutive at 1.
        rewrite <- E.
        ring.
      * discriminate.
  - intros [x H].
    unfold iscube.
    destruct a as [|p|p].
    + reflexivity.
    + simpl.
      rewrite <- H.
      destruct x as [|px|px].
      * reflexivity.
      * apply Z.eqb_refl.
      * simpl. 
        rewrite Z.mul_opp_opp.
        rewrite Z.mul_opp_opp.
        rewrite Z.mul_opp_opp.
        apply Z.eqb_refl.
    + simpl.
      rewrite <- H.
      destruct x as [|px|px].
      * reflexivity.
      * simpl.
        rewrite Z.mul_opp_opp.
        rewrite Z.mul_opp_opp.
        rewrite Z.mul_opp_opp.
        apply Z.eqb_refl.
      * apply Z.eqb_refl.
Qed.

Example test_iscube_1 : problem_77_spec 1%Z true.
Proof.
  unfold problem_77_spec.
  split.
  - intro H. exists 1. reflexivity.
  - intro H. reflexivity.
Qed.