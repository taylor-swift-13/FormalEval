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

Example test_will_it_fly : will_it_fly_spec [2; 2; 18; 0] 29 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Forward direction: false = true -> ... (contradiction) *)
    intros H.
    discriminate H.
  - (* Backward direction: (is_palindrome /\ sum <= w) -> false = true *)
    intros [Hpal _].
    unfold is_palindrome in Hpal.
    simpl in Hpal.
    (* Hpal : [2; 2; 18; 0] = [0; 18; 2; 2], which is false *)
    discriminate Hpal.
Qed.