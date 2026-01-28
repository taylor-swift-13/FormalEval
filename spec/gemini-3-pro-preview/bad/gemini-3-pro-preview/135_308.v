Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope Z_scope.

Definition can_arrange_spec (arr : list R) (res : Z) : Prop :=
  (res = -1 /\ 
   forall i : nat, (0 < i < length arr)%nat -> 
     (nth i arr 0%R >= nth (i - 1)%nat arr 0%R)%R)
  \/
  (0 < res < Z.of_nat (length arr) /\
   (nth (Z.to_nat res) arr 0%R < nth (Z.to_nat res - 1)%nat arr 0%R)%R /\
   forall k : Z, res < k < Z.of_nat (length arr) ->
     (nth (Z.to_nat k) arr 0%R >= nth (Z.to_nat k - 1)%nat arr 0%R)%R).

Example test_case : can_arrange_spec [37.45846213316932%R; -21.8131802318007%R; -18.630055685163583%R; -76.49298700358514%R; -63.655488885630994%R; 81.75342869524977%R; 96.86306070463999%R; 77.21191831561089%R; 22.028951203200748%R; -54.83341431889768%R] 9.
Proof.
  unfold can_arrange_spec.
  right.
  split.
  - simpl. lia.
  - split.
    + simpl. lra.
    + intros k Hk.
      simpl in Hk.
      lia.
Qed.