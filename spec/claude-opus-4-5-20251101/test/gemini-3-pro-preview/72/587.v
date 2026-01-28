Require Import List.
Require Import ZArith.
Require Import Psatz. (* For lia *)
Import ListNotations.

Open Scope Z_scope.

Fixpoint sum_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

Definition is_palindrome (l : list Z) : Prop :=
  l = rev l.

Definition will_it_fly_spec (q : list Z) (w : Z) (result : bool) : Prop :=
  result = true <-> (is_palindrome q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [19; 4; 8; 10; 12; 14; 16; 18; 21; 16] 20 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Forward direction: false = true -> ... (impossible) *)
    intros H.
    inversion H.
  - (* Backward direction: ... -> false = true (contradiction) *)
    intros [Hpal Hsum].
    unfold is_palindrome in Hpal.
    simpl in Hpal.
    (* The list is not a palindrome: 19 != 16 at the ends *)
    inversion Hpal.
Qed.