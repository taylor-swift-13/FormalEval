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

Lemma is_ceil_IZR : forall z : Z, is_ceil (IZR z) z.
Proof.
  intro z.
  unfold is_ceil.
  split.
  - lra.
  - lra.
Qed.

Lemma is_ceil_1_1_2 : is_ceil (1 + /10) 2.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_2_5_3 : is_ceil (2 + /2) 3.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_neg_3_7_neg_3 : is_ceil (-(3 + 7/10)) (-3).
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_neg_5_2_neg_5 : is_ceil (-(5 + /5)) (-5).
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1 + /10; 2 + /2; -(3 + 7/10); -(5 + /5); IZR (-6)] 83%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 3%Z; (-3)%Z; (-5)%Z; (-6)%Z].
  split.
  - constructor.
    + apply is_ceil_1_1_2.
    + constructor.
      * apply is_ceil_2_5_3.
      * constructor.
        -- apply is_ceil_neg_3_7_neg_3.
        -- constructor.
           ++ apply is_ceil_neg_5_2_neg_5.
           ++ constructor.
              ** apply is_ceil_IZR.
              ** constructor.
  - simpl.
    reflexivity.
Qed.