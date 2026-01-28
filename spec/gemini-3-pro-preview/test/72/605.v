Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> (q = rev q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [7; 2; 5; 5; 5] 1 false.
Proof.
  (* Unfold the specification definition *)
  unfold will_it_fly_spec.

  (* Split the bi-implication (<->) *)
  split.

  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.

  - (* Right to Left: (Palindrome /\ Sum condition) -> false = true *)
    intros [Hpal Hsum].
    unfold sum_list in Hsum.
    simpl in Hsum.
    (* 24 <= 1 is a contradiction *)
    lia.
Qed.