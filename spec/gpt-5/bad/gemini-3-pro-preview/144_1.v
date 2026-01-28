Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Parameter parse_frac : string -> nat -> nat -> Prop.

Definition simplify_spec (x n : string) (res : bool) : Prop :=
  exists x1 x2 n1 n2 : nat,
    parse_frac x x1 x2 /\
    parse_frac n n1 n2 /\
    0 < x1 /\ 0 < x2 /\ 0 < n1 /\ 0 < n2 /\
    (res = true <-> Nat.modulo (x1 * n1) (x2 * n2) = 0).

(* Axioms to satisfy the abstract parse_frac parameter for the specific test case *)
Axiom parse_1_5 : parse_frac "1/5" 1 5.
Axiom parse_5_1 : parse_frac "5/1" 5 1.

Example test_simplify : simplify_spec "1/5" "5/1" true.
Proof.
  unfold simplify_spec.
  exists 1, 5, 5, 1.
  (* 
     repeat split will break down all conjunctions (/\) and the iff (<->).
     The structure is: P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6 /\ (P7 <-> P8).
     This results in 8 subgoals: P1, P2, P3, P4, P5, P6, P7->P8, P8->P7.
  *)
  repeat split.
  - (* parse_frac "1/5" 1 5 *)
    apply parse_1_5.
  - (* parse_frac "5/1" 5 1 *)
    apply parse_5_1.
  - (* 0 < 1 *)
    lia.
  - (* 0 < 5 *)
    lia.
  - (* 0 < 5 *)
    lia.
  - (* 0 < 1 *)
    lia.
  - (* Forward direction: true = true -> (1 * 5) mod (5 * 1) = 0 *)
    intros _.
    simpl. (* reduces 1*5 to 5 and 5*1 to 5 *)
    rewrite Nat.mod_same.
    + reflexivity.
    + lia. (* 5 <> 0 *)
  - (* Backward direction: (1 * 5) mod (5 * 1) = 0 -> true = true *)
    intros _.
    reflexivity.
Qed.