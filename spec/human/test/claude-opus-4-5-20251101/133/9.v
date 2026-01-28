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

Lemma is_ceil_neg1_4 : is_ceil (-1.4) (-1)%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_17_9 : is_ceil 17.9 18%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_18_9 : is_ceil 18.9 19%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_19_9 : is_ceil 19.9 20%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Example test_problem_133 :
  problem_133_spec [-1.4; 17.9; 18.9; 19.9] 1086%Z.
Proof.
  unfold problem_133_spec.
  exists [(-1)%Z; 18%Z; 19%Z; 20%Z].
  split.
  - constructor.
    + apply is_ceil_neg1_4.
    + constructor.
      * apply is_ceil_17_9.
      * constructor.
        -- apply is_ceil_18_9.
        -- constructor.
           ++ apply is_ceil_19_9.
           ++ constructor.
  - simpl.
    reflexivity.
Qed.