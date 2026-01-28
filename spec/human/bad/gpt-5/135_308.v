Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Arith.Arith.
Require Import Lia.
Require Import Coq.Reals.Lra.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

Definition drop_at (lst : list R) (k : nat) : Prop :=
  (1 <= k)%nat /\ (k < length lst)%nat /\
  match nth_error lst k, nth_error lst (k - 1) with
  | Some y, Some x => y < x
  | _, _ => False
  end.

Definition problem_135_pre (lst : list R) : Prop := NoDup lst.

Definition problem_135_spec (lst : list R) (r : Z) : Prop :=
  (r = -1 /\ (forall k, ~ drop_at lst k))
  \/
  (exists k : nat,
      r = Z.of_nat k /\
      drop_at lst k /\
      (forall j : nat, drop_at lst j -> (j <= k)%nat)).

Example can_arrange_example_1 :
  problem_135_spec
    [37.45846213316932%R; -21.8131802318007%R; -18.630055685163583%R; -76.49298700358514%R; -63.655488885630994%R; 81.75342869524977%R; 96.86306070463999%R; 77.21191831561089%R; 22.028951203200748%R; -54.83341431889768%R]
    9%Z.
Proof.
  unfold problem_135_spec.
  right.
  exists 9%nat.
  split; [reflexivity |].
  split.
  - unfold drop_at.
    split; [lia|].
    split.
    + simpl; lia.
    + simpl; lra.
  - intros j Hj.
    destruct Hj as [Hj1 [Hjlen Hjmatch]].
    simpl in Hjlen.
    lia.
Qed.