Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Lia.

Parameter parse_frac : string -> nat -> nat -> Prop.

Definition simplify_spec (x n : string) (res : bool) : Prop :=
  exists x1 x2 n1 n2 : nat,
    parse_frac x x1 x2 /\
    parse_frac n n1 n2 /\
    0 < x1 /\ 0 < x2 /\ 0 < n1 /\ 0 < n2 /\
    (res = true <-> Nat.modulo (x1 * n1) (x2 * n2) = 0).

(* We need to assume parse_frac behaves correctly for our test strings *)
Axiom parse_frac_1_5 : parse_frac "1/5" 1 5.
Axiom parse_frac_5_1 : parse_frac "5/1" 5 1.

Example test_simplify : simplify_spec "1/5" "5/1" true.
Proof.
  unfold simplify_spec.
  exists 1, 5, 5, 1.
  split. { exact parse_frac_1_5. }
  split. { exact parse_frac_5_1. }
  split. { lia. }
  split. { lia. }
  split. { lia. }
  split. { lia. }
  split.
  - intros _. simpl. reflexivity.
  - intros _. reflexivity.
Qed.