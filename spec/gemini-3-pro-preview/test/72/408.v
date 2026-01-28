Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> (q = rev q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [2; 2; 18; 0] 29 false.
Proof.
  (* Unfold the specification definition *)
  unfold will_it_fly_spec.

  (* Split the bi-implication (<->) *)
  split.

  - (* Left to Right: false = true -> (Palindrome /\ Sum condition) *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.

  - (* Right to Left: (Palindrome /\ Sum condition) -> false = true *)
    intros [H_pal H_sum].
    (* Verify that q is NOT a palindrome *)
    simpl in H_pal.
    (* [2; 2; 18; 0] <> [0; 18; 2; 2], so H_pal is a contradiction *)
    discriminate H_pal.
Qed.