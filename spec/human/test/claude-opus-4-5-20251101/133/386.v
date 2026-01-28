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

Lemma is_ceil_neg_3_4 : is_ceil (-3.4) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_6_773948579844583 : is_ceil (-6.773948579844583) (-6)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_5_1 : is_ceil (-5.1) (-5)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_4_6 : is_ceil (-4.6) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_2_98440779706064 : is_ceil (-2.98440779706064) (-2)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [IZR 2; -3.4; -6.773948579844583; IZR (-6); -5.1; IZR (-6); -4.6; -2.98440779706064; -6.773948579844583; IZR 2] 206%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; (-3)%Z; (-6)%Z; (-6)%Z; (-5)%Z; (-6)%Z; (-4)%Z; (-2)%Z; (-6)%Z; 2%Z].
  split.
  - constructor.
    + apply is_ceil_IZR.
    + constructor.
      * apply is_ceil_neg_3_4.
      * constructor.
        -- apply is_ceil_neg_6_773948579844583.
        -- constructor.
           ++ apply is_ceil_IZR.
           ++ constructor.
              ** apply is_ceil_neg_5_1.
              ** constructor.
                 --- apply is_ceil_IZR.
                 --- constructor.
                     +++ apply is_ceil_neg_4_6.
                     +++ constructor.
                         *** apply is_ceil_neg_2_98440779706064.
                         *** constructor.
                             ---- apply is_ceil_neg_6_773948579844583.
                             ---- constructor.
                                  ++++ apply is_ceil_IZR.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.