Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> (q = rev q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [10; 2; 2; 1; 0; 2] 17 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Left to Right: false = true -> ... (Contradiction) *)
    intros H.
    inversion H.
  - (* Right to Left: (Palindrome /\ Sum condition) -> false = true *)
    intros [H_pal H_sum].
    (* Verify q = rev q is false *)
    simpl in H_pal.
    (* The lists [10; 2; ...] and [2; 0; ...] are not equal *)
    discriminate H_pal.
Qed.