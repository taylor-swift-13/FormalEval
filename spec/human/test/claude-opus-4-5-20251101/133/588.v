Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition is_ceil (x : R) (z : Z) : Prop :=
  (IZR z - 1 < x) /\ (x <= IZR z).

Definition problem_133_pre (lst : list R) : Prop := True.

Definition problem_133_spec (lst : list R) (s : Z) : Prop :=
  exists zs : list Z,
    Forall2 is_ceil lst zs /\
    s = fold_right Z.add 0%Z (map (fun z => Z.mul z z) zs).

Lemma is_ceil_neg1 : is_ceil (-1.1) (-1)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_neg3 : is_ceil (-3.7) (-3)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_neg4a : is_ceil (-4.6) (-4)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_neg2 : is_ceil (-2.8396588982482287) (-2)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_pos5 : is_ceil (5.2) (6)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_neg4b : is_ceil (-4.6) (-4)%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Example test_problem_133 :
  problem_133_spec [-1.1; -3.7; -4.6; -2.8396588982482287; 5.2; -4.6] 82%Z.
Proof.
  unfold problem_133_spec.
  exists [(-1)%Z; (-3)%Z; (-4)%Z; (-2)%Z; 6%Z; (-4)%Z].
  split.
  - constructor.
    + apply is_ceil_neg1.
    + constructor.
      * apply is_ceil_neg3.
      * constructor.
        -- apply is_ceil_neg4a.
        -- constructor.
           ++ apply is_ceil_neg2.
           ++ constructor.
              ** apply is_ceil_pos5.
              ** constructor.
                 --- apply is_ceil_neg4b.
                 --- constructor.
  - simpl.
    reflexivity.
Qed.