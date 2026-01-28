Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Helper for factorial in Z to avoid nat overflow *)
Fixpoint fact_Z (n : nat) : Z :=
  match n with
  | 0%nat => 1
  | S p => Z.of_nat n * fact_Z p
  end.

(* Specification definition *)
Definition problem_106_pre (n : nat) : Prop := True.

Definition problem_106_spec (n : nat) (l : list Z) : Prop :=
  let sum := fun (i : nat) => (Z.of_nat i * (Z.of_nat i + 1)) / 2 in
  length l = n /\
  (forall i : nat, (1 <= i)%nat -> (i <= n)%nat -> nth_error l (i - 1) = Some (if Nat.even i then fact_Z i else sum i)).

(* Implementation *)
Definition solve_106 (n : nat) : list Z :=
  map (fun i => if Nat.even i then fact_Z i else (Z.of_nat i * (Z.of_nat i + 1)) / 2) (seq 1 n).

(* Proof of Correctness *)
Lemma solve_106_correct : forall n, problem_106_pre n -> problem_106_spec n (solve_106 n).
Proof.
  intros n _.
  unfold problem_106_spec, solve_106.
  split.
  - (* Check length *)
    rewrite length_map.
    rewrite length_seq.
    reflexivity.
  - (* Check elements *)
    intros i Hge Hle.
    rewrite nth_error_map.
    rewrite nth_error_seq.
    (* Resolve the condition (i - 1 < n) introduced by nth_error_seq *)
    assert (Hlt: (i - 1 < n)%nat) by lia.
    apply Nat.ltb_lt in Hlt.
    rewrite Hlt.
    (* Simplify the value (1 + (i - 1)) to i *)
    replace (1 + (i - 1))%nat with i by lia.
    simpl.
    reflexivity.
Qed.

(* Test Case Proof *)
Lemma example_106 : problem_106_spec 21 [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200; 120; 20922789888000; 153; 6402373705728000; 190; 2432902008176640000; 231].
Proof.
  (* Verify that solve_106 21 produces the expected list *)
  assert (H_eq: solve_106 21 = [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200; 120; 20922789888000; 153; 6402373705728000; 190; 2432902008176640000; 231]).
  { reflexivity. }
  
  (* Apply the general correctness theorem *)
  rewrite <- H_eq.
  apply solve_106_correct.
  exact I.
Qed.