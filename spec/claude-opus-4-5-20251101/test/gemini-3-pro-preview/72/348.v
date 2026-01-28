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

Example test_will_it_fly : will_it_fly_spec [7] 6 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Forward direction: false = true -> ... (contradiction) *)
    intros H.
    discriminate H.
  - (* Backward direction: (is_palindrome /\ sum <= w) -> false = true *)
    intros [_ Hsum].
    (* Hsum states sum_list [7] <= 6, which is 7 <= 6 *)
    simpl in Hsum.
    lia.
Qed.