Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0%Z l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_Z q <= w.

Example test_will_it_fly : will_it_fly_spec [1; 2; 2; 1; 0; 1] 7 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Right to Left: ... -> false = true *)
    intros [Hpal _].
    (* We need to show that Hpal (palindrome equality) is false. *)
    (* q = [1; 2; 2; 1; 0; 1], rev q = [1; 0; 1; 2; 2; 1] *)
    simpl in Hpal.
    (* Hpal simplifies to [1; 2; 2; 1; 0; 1] = [1; 0; 1; 2; 2; 1]. *)
    (* The heads match (1=1), but the next elements (2 vs 0) do not. *)
    (* congruence can solve this equality contradiction automatically. *)
    congruence.
Qed.