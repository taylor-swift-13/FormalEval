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

Lemma is_ceil_2 : is_ceil (11/10) 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg3 : is_ceil (-37/10) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg4 : is_ceil (-46/10) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg4_2 : is_ceil (-4276874536373084/1000000000000000) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg5 : is_ceil (-52/10) (-5)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg9 : is_ceil (-999/100) (-9)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3 : is_ceil (25/10) 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [11/10; -37/10; -46/10; -4276874536373084/1000000000000000; -52/10; -999/100; IZR (-6); -999/100; -999/100; 25/10] 358%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; (-3)%Z; (-4)%Z; (-4)%Z; (-5)%Z; (-9)%Z; (-6)%Z; (-9)%Z; (-9)%Z; 3%Z].
  split.
  - constructor.
    + apply is_ceil_2.
    + constructor.
      * apply is_ceil_neg3.
      * constructor.
        -- apply is_ceil_neg4.
        -- constructor.
           ++ apply is_ceil_neg4_2.
           ++ constructor.
              ** apply is_ceil_neg5.
              ** constructor.
                 --- apply is_ceil_neg9.
                 --- constructor.
                     +++ apply is_ceil_IZR.
                     +++ constructor.
                         *** apply is_ceil_neg9.
                         *** constructor.
                             ---- apply is_ceil_neg9.
                             ---- constructor.
                                  ++++ apply is_ceil_3.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.