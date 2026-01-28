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

Lemma is_ceil_0 : is_ceil (-0.6763327164350088) 0%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_from_2_5 : is_ceil 2.5 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg3_from_neg3_7 : is_ceil (-3.7) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg4_from_neg4_6 : is_ceil (-4.6) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg2_from_neg2_8 : is_ceil (-2.8396588982482287) (-2)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [(-0.6763327164350088); 2.5; (-3.7); (-4.6); (-4.6); (-2.8396588982482287); IZR 6; IZR 6; IZR 6; IZR 6] 198%Z.
Proof.
  unfold problem_133_spec.
  exists [0%Z; 3%Z; (-3)%Z; (-4)%Z; (-4)%Z; (-2)%Z; 6%Z; 6%Z; 6%Z; 6%Z].
  split.
  - constructor.
    + apply is_ceil_0.
    + constructor.
      * apply is_ceil_3_from_2_5.
      * constructor.
        -- apply is_ceil_neg3_from_neg3_7.
        -- constructor.
           ++ apply is_ceil_neg4_from_neg4_6.
           ++ constructor.
              ** apply is_ceil_neg4_from_neg4_6.
              ** constructor.
                 --- apply is_ceil_neg2_from_neg2_8.
                 --- constructor.
                     +++ apply is_ceil_IZR.
                     +++ constructor.
                         *** apply is_ceil_IZR.
                         *** constructor.
                             ---- apply is_ceil_IZR.
                             ---- constructor.
                                  ++++ apply is_ceil_IZR.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.