Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Import ListNotations.

Open Scope Z_scope.

Definition freq (z : Z) (l : list Z) : nat :=
  length (filter (fun x => Z.eqb x z) l).

Definition search_spec (lst : list Z) (ans : Z) : Prop :=
  Forall (fun x => x > 0) lst /\
  lst <> nil /\
  ((exists n : Z, n > 0 /\ Z.of_nat (freq n lst) >= n) ->
     ans > 0 /\ Z.of_nat (freq ans lst) >= ans /\
     forall n : Z, n > 0 -> Z.of_nat (freq n lst) >= n -> n <= ans) /\
  ((forall n : Z, ~(n > 0 /\ Z.of_nat (freq n lst) >= n)) ->
     ans = -1).

Example test_case : search_spec [5; 5; 5; 5; 1] 1.
Proof.
  unfold search_spec, freq.
  repeat split.
  - (* Prove Forall x > 0 *)
    repeat constructor; lia.
  - (* Prove lst <> nil *)
    discriminate.
  - (* Prove implication: if valid n exists, ans=1 is correct *)
    intros _. repeat split.
    + (* ans > 0 *)
      lia.
    + (* freq ans >= ans *)
      simpl. lia.
    + (* forall n, valid n -> n <= ans *)
      intros n Hpos Hcond.
      simpl in Hcond.
      destruct (Z.eqb_spec 5 n).
      * (* Case n = 5 *)
        subst. simpl in Hcond. lia.
      * (* Case n <> 5 *)
        destruct (Z.eqb_spec 1 n).
        -- (* Case n = 1 *)
           subst. lia.
        -- (* Case n <> 5 and n <> 1 *)
           (* Replace boolean comparisons with false in Hcond *)
           replace (5 =? n) with false in Hcond by (symmetry; apply Z.eqb_neq; lia).
           replace (1 =? n) with false in Hcond by (symmetry; apply Z.eqb_neq; lia).
           simpl in Hcond.
           lia.
  - (* Prove implication: if no valid n exists, ans=-1 (contradiction here) *)
    intros Hcontra.
    exfalso.
    (* Show that n=1 is a valid witness to contradict Hcontra *)
    apply (Hcontra 1).
    split.
    + lia.
    + simpl. lia.
Qed.