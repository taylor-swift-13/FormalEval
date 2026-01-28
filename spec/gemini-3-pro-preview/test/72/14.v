Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> (q = rev q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [1; 2; 3] 10 false.
Proof.
  (* Unfold the specification definition *)
  unfold will_it_fly_spec.
  
  (* Split the bi-implication (<->) *)
  split.
  
  - (* Left to Right: false = true -> ... (Contradiction) *)
    intros H.
    discriminate H.

  - (* Right to Left: (Palindrome /\ Sum condition) -> false = true *)
    intros [Hpal Hsum].
    (* Verify that q is not a palindrome: [1; 2; 3] <> [3; 2; 1] *)
    simpl in Hpal.
    discriminate Hpal.
Qed.