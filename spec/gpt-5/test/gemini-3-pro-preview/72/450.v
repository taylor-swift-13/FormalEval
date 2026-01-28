Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0%Z l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_Z q <= w.

Example test_will_it_fly : will_it_fly_spec [2; 2; 1; 0; 2; 2] 30 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Left to Right implication: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left implication: ... -> false = true *)
    intros [H_palindrome _].
    (* The list is not a palindrome, so H_palindrome implies a contradiction *)
    simpl in H_palindrome.
    (* [2; 2; 1; 0; 2; 2] = [2; 2; 0; 1; 2; 2] contains a mismatch *)
    discriminate.
Qed.