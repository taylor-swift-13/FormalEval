Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Lia.

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

Definition collatz_14 : list Z :=
  [14; 7; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].

Definition odd_collatz_14 : list Z :=
  [7; 11; 17; 13; 5; 1].

Definition sorted_odd_14 : list Z :=
  [1; 5; 7; 11; 13; 17].

Lemma collatz_aux_14_eq : collatz_aux 14 18 = collatz_14.
Proof. native_compute. reflexivity. Qed.

Lemma filter_odd_14_eq : filter (fun x => Z.odd x) collatz_14 = odd_collatz_14.
Proof. native_compute. reflexivity. Qed.

Lemma perm_sorted_odd : Permutation sorted_odd_14 odd_collatz_14.
Proof.
  unfold sorted_odd_14, odd_collatz_14.
  apply Permutation_sym.
  eapply perm_trans.
  - apply perm_swap.
  - apply perm_skip.
    eapply perm_trans.
    - apply perm_swap.
    - apply perm_skip.
      eapply perm_trans.
      + apply perm_swap.
      + apply perm_skip.
        eapply perm_trans.
        * apply perm_swap.
        * apply perm_skip.
          apply perm_swap.
Qed.

Lemma sorted_result : Sorted Z.le sorted_odd_14.
Proof.
  unfold sorted_odd_14.
  apply Sorted_cons. apply Sorted_cons. apply Sorted_cons. 
  apply Sorted_cons. apply Sorted_cons. apply Sorted_cons.
  apply Sorted_nil.
  apply HdRel_nil.
  apply HdRel_cons. lia.
  apply HdRel_cons. lia.
  apply HdRel_cons. lia.
  apply HdRel_cons. lia.
  apply HdRel_cons. lia.
Qed.

Example problem_123_test :
  problem_123_spec 14 [1%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z].
Proof.
  unfold problem_123_spec.
  exists collatz_14.
  split.
  - unfold collatz_list.
    exists 18%nat.
    split.
    + exact collatz_aux_14_eq.
    + native_compute. reflexivity.
  - split.
    + rewrite filter_odd_14_eq.
      exact perm_sorted_odd.
    + exact sorted_result.
Qed.