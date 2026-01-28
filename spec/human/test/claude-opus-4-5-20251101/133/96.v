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

Example test_problem_133 :
  problem_133_spec [IZR 2; IZR 3; IZR 1; IZR (-5); IZR 2; IZR 4; IZR (-5)] 84%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 3%Z; 1%Z; (-5)%Z; 2%Z; 4%Z; (-5)%Z].
  split.
  - constructor.
    + apply is_ceil_IZR.
    + constructor.
      * apply is_ceil_IZR.
      * constructor.
        -- apply is_ceil_IZR.
        -- constructor.
           ++ apply is_ceil_IZR.
           ++ constructor.
              ** apply is_ceil_IZR.
              ** constructor.
                 --- apply is_ceil_IZR.
                 --- constructor.
                     +++ apply is_ceil_IZR.
                     +++ constructor.
  - simpl.
    reflexivity.
Qed.