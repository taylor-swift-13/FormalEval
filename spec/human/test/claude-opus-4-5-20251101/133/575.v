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

Lemma is_ceil_2 : is_ceil 1.1 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4 : is_ceil 3.454312388429943 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg3 : is_ceil (-3.7) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg6 : is_ceil (-6.198816864183874) (-6)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg4 : is_ceil (-4.276874536373084) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg5 : is_ceil (-5.2) (-5)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg9 : is_ceil (-9.99) (-9)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1.1; 3.454312388429943; -3.7; -6.198816864183874; -4.276874536373084; -5.2; -9.99; IZR (-6)] 223%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 4%Z; (-3)%Z; (-6)%Z; (-4)%Z; (-5)%Z; (-9)%Z; (-6)%Z].
  split.
  - constructor.
    + apply is_ceil_2.
    + constructor.
      * apply is_ceil_4.
      * constructor.
        -- apply is_ceil_neg3.
        -- constructor.
           ++ apply is_ceil_neg6.
           ++ constructor.
              ** apply is_ceil_neg4.
              ** constructor.
                 --- apply is_ceil_neg5.
                 --- constructor.
                     +++ apply is_ceil_neg9.
                     +++ constructor.
                         *** apply is_ceil_IZR.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.