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

Lemma is_ceil_01_1 : is_ceil (1/10) 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_67_7 : is_ceil (67/10) 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_55_6 : is_ceil (55/10) 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg65_neg6 : is_ceil (-(65/10)) (-6)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_32_4 : is_ceil (32/10) 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_46_5 : is_ceil (46/10) 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg999_neg9 : is_ceil (-(999/100)) (-9)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_51_6 : is_ceil (51/10) 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1/10; 67/10; 55/10; -(65/10); 32/10; 46/10; -(999/100); 51/10; 67/10; 67/10] 378%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 7%Z; 6%Z; (-6)%Z; 4%Z; 5%Z; (-9)%Z; 6%Z; 7%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_01_1.
    + constructor.
      * apply is_ceil_67_7.
      * constructor.
        -- apply is_ceil_55_6.
        -- constructor.
           ++ apply is_ceil_neg65_neg6.
           ++ constructor.
              ** apply is_ceil_32_4.
              ** constructor.
                 --- apply is_ceil_46_5.
                 --- constructor.
                     +++ apply is_ceil_neg999_neg9.
                     +++ constructor.
                         *** apply is_ceil_51_6.
                         *** constructor.
                             ---- apply is_ceil_67_7.
                             ---- constructor.
                                  ++++ apply is_ceil_67_7.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.