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
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3 : is_ceil 2.211013714786509 3%Z.
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

Lemma is_ceil_5a : is_ceil 4.6 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6a : is_ceil 5.147008615293544 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6b : is_ceil 5.1 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [-1.1; 2.211013714786509; -3.7; 4.6; 5.147008615293544; 5.1] 116%Z.
Proof.
  unfold problem_133_spec.
  exists [(-1)%Z; 3%Z; (-3)%Z; 5%Z; 6%Z; 6%Z].
  split.
  - constructor.
    + apply is_ceil_neg1.
    + constructor.
      * apply is_ceil_3.
      * constructor.
        -- apply is_ceil_neg3.
        -- constructor.
           ++ apply is_ceil_5a.
           ++ constructor.
              ** apply is_ceil_6a.
              ** constructor.
                 --- apply is_ceil_6b.
                 --- constructor.
  - simpl.
    reflexivity.
Qed.