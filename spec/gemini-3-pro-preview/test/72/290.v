Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> (q = rev q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [1; 2; 11; 4; 5; 6] 10 false.
Proof.
  (* Unfold the specification definition *)
  unfold will_it_fly_spec.
  
  (* Split the bi-implication (<->) *)
  split.
  
  - (* Left to Right: false = true -> ... *)
    intros H.
    (* Premise is false, so implication holds trivially *)
    inversion H.

  - (* Right to Left: (Palindrome /\ Sum condition) -> false = true *)
    intros [Hpal Hsum].
    (* Verify that the list is not a palindrome to derive a contradiction *)
    simpl in Hpal.
    (* The list [1; 2; 11; 4; 5; 6] is not equal to [6; 5; 4; 11; 2; 1] *)
    discriminate Hpal.
Qed.