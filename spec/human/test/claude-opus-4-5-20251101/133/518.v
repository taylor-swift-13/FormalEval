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

Lemma is_ceil_neg6 : is_ceil (IZR (-6)) (-6)%Z.
Proof.
  apply is_ceil_IZR.
Qed.

Lemma is_ceil_3_0179 : is_ceil 3.0179751175777536 4%Z.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_1 : is_ceil (IZR 1) 1%Z.
Proof.
  apply is_ceil_IZR.
Qed.

Lemma is_ceil_neg3_4 : is_ceil (-3.4) (-3)%Z.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_0_5 : is_ceil 0.5 1%Z.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_neg5_1 : is_ceil (-5.1) (-5)%Z.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_neg7 : is_ceil (IZR (-7)) (-7)%Z.
Proof.
  apply is_ceil_IZR.
Qed.

Example test_problem_133 :
  problem_133_spec [IZR (-6); 3.0179751175777536; IZR 1; -3.4; 0.5; -5.1; IZR (-7); -5.1] 162%Z.
Proof.
  unfold problem_133_spec.
  exists [(-6)%Z; 4%Z; 1%Z; (-3)%Z; 1%Z; (-5)%Z; (-7)%Z; (-5)%Z].
  split.
  - constructor.
    + apply is_ceil_neg6.
    + constructor.
      * apply is_ceil_3_0179.
      * constructor.
        -- apply is_ceil_1.
        -- constructor.
           ++ apply is_ceil_neg3_4.
           ++ constructor.
              ** apply is_ceil_0_5.
              ** constructor.
                 --- apply is_ceil_neg5_1.
                 --- constructor.
                     +++ apply is_ceil_neg7.
                     +++ constructor.
                         *** apply is_ceil_neg5_1.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.