Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint collatz_aux (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if Z.eqb n 1 then [1]
    else
      let next := if Z.even n then n / 2 else 3 * n + 1 in
      n :: collatz_aux next fuel'
  end.

Definition collatz_list (n : Z) (l : list Z) : Prop :=
  exists fuel, collatz_aux n fuel = l /\ last l 0 = 1.

Definition problem_123_pre (n : Z) : Prop := n > 0.

Definition problem_123_spec (n : Z) (result : list Z) : Prop :=
  exists (c_seq : list Z),
    collatz_list n c_seq /\
    Permutation result (filter (fun x => Z.odd x) c_seq) /\
    Sorted Z.le result.

Definition collatz_14_seq : list Z :=
  [14;7;22;11;34;17;52;26;13;40;20;10;5;16;8;4;2;1].

(* Auxiliary lemma: collatz_aux 14 20 = collatz_14_seq *)
Lemma collatz_aux_14_20_eq :
  collatz_aux 14 20 = collatz_14_seq.
Proof.
  (* We'll do induction on fuel manually aligned with collatz_14_seq *)
  simpl.
  (* To avoid revert error, use an explicit auxiliary lemma with Fixpoint *)
  (* Define a local recursive helper matching fuel and collatz_14_seq *)
  remember 14 as n.
  revert n.
  (* We prove more general lemma: collatz_aux n 20 equals collatz sequence (that we provide) *)
  assert (forall n fuel,
            fuel = 0 -> collatz_aux n fuel = [] /\ True) as H0.
  { intros; subst; simpl; auto. }
  assert (forall n fuel,
            fuel = 1 ->
            (if Z.eqb n 1 then collatz_aux n fuel = [1] else
              let next := if Z.even n then n / 2 else 3 * n + 1 in
              collatz_aux n fuel = [n])) as H1.
  { intros n0 [|f0] Heq; simpl in *; try lia; try reflexivity.
    destruct (Z.eqb n0 1); reflexivity. }
  (* Prove by induction on fuel S fuel' for 20 *)
  revert n.
  induction 20 as [|fuel' IH]; intros n0; simpl.
  - reflexivity.
  - destruct (Z.eqb n0 1) eqn:E.
    + apply Z.eqb_eq in E; subst; simpl; reflexivity.
    + remember (if Z.even n0 then n0 / 2 else 3 * n0 + 1) as next.
      f_equal.
      apply IH.
Qed.

Example test_case_14 :
  problem_123_spec 14 [1;5;7;11;13;17].
Proof.
  unfold problem_123_spec.
  exists collatz_14_seq.
  split.
  - unfold collatz_list.
    exists 20%nat.
    split.
    + apply collatz_aux_14_20_eq.
    + simpl. reflexivity.
  - split.
    + (* Permutation between result and filter odd collatz_14_seq *)
      assert (filter (fun x => Z.odd x) collatz_14_seq = [7;11;17;13;5;1]) as Hfilter.
      {
        unfold collatz_14_seq; simpl.
        repeat match goal with
        | |- context[Z.odd ?x] =>
          let H := fresh in
          destruct (Z.odd x) eqn:H; simpl
        end; try reflexivity.
      }
      rewrite Hfilter.
      (* Prove Permutation [1;5;7;11;13;17] [7;11;17;13;5;1] *)
      apply Permutation_sym.
      (* Generated permutation by swaps *)
      apply Permutation_rearrangement.
      (* explicit permutation by swaps *)
      repeat (try apply Permutation_swap).
      apply Permutation_refl.
    + (* Sorted Z.le [1;5;7;11;13;17] *)
      unfold Sorted; repeat constructor; lia.
Qed.