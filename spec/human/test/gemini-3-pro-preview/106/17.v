Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Factorial.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Specification definition *)
Definition problem_106_pre (n : nat) : Prop := True.

Definition problem_106_spec (n : nat) (l : list nat) : Prop :=
  let sum := fun i => Nat.div (i * (i + 1)) 2 in
  length l = n /\
  (forall i, 1 <= i -> i <= n -> nth_error l (i - 1) = Some (if Nat.even i then fact i else sum i)).

(* Implementation *)
Definition solve_106 (n : nat) : list nat :=
  map (fun i => if Nat.even i then fact i else Nat.div (i * (i + 1)) 2) (seq 1 n).

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
    assert (Hlt: i - 1 < n) by lia.
    apply Nat.ltb_lt in Hlt.
    rewrite Hlt.
    (* Simplify the value (1 + (i - 1)) to i *)
    replace (1 + (i - 1)) with i by lia.
    simpl.
    reflexivity.
Qed.

(* Test Case Proof *)
Lemma example_106 : problem_106_spec 19 
  [1; fact 2; 6; fact 4; 15; fact 6; 28; fact 8; 45; fact 10; 66; fact 12; 91; fact 14; 120; fact 16; 153; fact 18; 190].
Proof.
  (* Make fact opaque to prevent expansion of large factorials which would cause timeout/overflow in nat *)
  Opaque fact.
  (* Verify that solve_106 19 produces the expected list *)
  assert (H_eq: solve_106 19 = [1; fact 2; 6; fact 4; 15; fact 6; 28; fact 8; 45; fact 10; 66; fact 12; 91; fact 14; 120; fact 16; 153; fact 18; 190]).
  { 
    simpl. 
    reflexivity. 
  }
  
  (* Apply the general correctness theorem *)
  rewrite <- H_eq.
  apply solve_106_correct.
  exact I.
Qed.