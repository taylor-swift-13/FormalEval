Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

(* Specification Definitions *)

Fixpoint sum_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

Definition is_palindrome (l : list Z) : Prop :=
  l = rev l.

Definition will_it_fly_spec (q : list Z) (w : Z) (result : bool) : Prop :=
  result = true <-> (is_palindrome q /\ sum_list q <= w).

(* Test Case Proof *)

Theorem test_will_it_fly : will_it_fly_spec [3; 2; 3] 9 true.
Proof.
  (* Unfold the specification to expose the logical structure *)
  unfold will_it_fly_spec.

  (* The goal is a bi-implication (A <-> B). We split into A -> B and B -> A *)
  split.

  - (* Case: result = true -> (is_palindrome /\ sum <= w) *)
    intros H_true.
    split.
    + (* Prove is_palindrome *)
      unfold is_palindrome.
      (* Simplify the list reversal *)
      simpl.
      (* [3; 2; 3] = [3; 2; 3] is true by reflexivity *)
      reflexivity.
    + (* Prove sum_list <= w *)
      (* Simplify the sum calculation: 3 + 2 + 3 = 8 *)
      simpl.
      (* Prove 8 <= 9 using Linear Integer Arithmetic *)
      lia.

  - (* Case: (is_palindrome /\ sum <= w) -> result = true *)
    intros H_cond.
    (* The goal is true = true, which is trivial *)
    reflexivity.
Qed.