Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> (q = rev q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [2; 3; 2] 7 true.
Proof.
  (* Unfold the specification definition *)
  unfold will_it_fly_spec.
  
  (* Split the bi-implication (<->) *)
  split.
  
  - (* Left to Right: true = true -> (Palindrome /\ Sum condition) *)
    intros _.
    split.
    + (* Sub-goal 1: Verify q = rev q *)
      simpl.
      reflexivity.
    + (* Sub-goal 2: Verify sum_list q <= w *)
      unfold sum_list.
      simpl.
      (* 2 + 3 + 2 + 0 <= 7 -> 7 <= 7 *)
      lia.

  - (* Right to Left: (Palindrome /\ Sum condition) -> true = true *)
    intros _.
    reflexivity.
Qed.