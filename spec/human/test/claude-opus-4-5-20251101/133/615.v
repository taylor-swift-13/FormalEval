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

Lemma is_ceil_example_1 : is_ceil 0.061283494508126014 1%Z.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_example_2 : is_ceil 1.5 2%Z.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_example_3 : is_ceil 3.2 4%Z.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_example_4 : is_ceil 6.851261387881998 7%Z.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_example_5 : is_ceil 7.859916102380617 8%Z.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_example_6 : is_ceil 8.634480834505068 9%Z.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_example_7 : is_ceil (-0.9061133911750052) 0%Z.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_example_8 : is_ceil 6.7 7%Z.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_example_9 : is_ceil 5.147008615293544 6%Z.
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Example test_problem_133 :
  problem_133_spec [0.061283494508126014; 1.5; 3.2; 6.851261387881998; 7.859916102380617; 8.634480834505068; -0.9061133911750052; 6.7; 5.147008615293544; 6.851261387881998] 349%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 2%Z; 4%Z; 7%Z; 8%Z; 9%Z; 0%Z; 7%Z; 6%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_example_1.
    + constructor.
      * apply is_ceil_example_2.
      * constructor.
        -- apply is_ceil_example_3.
        -- constructor.
           ++ apply is_ceil_example_4.
           ++ constructor.
              ** apply is_ceil_example_5.
              ** constructor.
                 --- apply is_ceil_example_6.
                 --- constructor.
                     +++ apply is_ceil_example_7.
                     +++ constructor.
                         *** apply is_ceil_example_8.
                         *** constructor.
                             ---- apply is_ceil_example_9.
                             ---- constructor.
                                  ++++ apply is_ceil_example_4.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.