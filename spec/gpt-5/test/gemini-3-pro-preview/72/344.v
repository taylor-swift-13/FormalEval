Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0%Z l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_Z q <= w.

Example test_will_it_fly : will_it_fly_spec [14; 2; 4; 5; 3; 3] 6 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left: ... -> false = true *)
    intros [_ Hsum].
    (* The sum condition fails: 31 <= 6 is false *)
    unfold sum_Z in Hsum.
    simpl in Hsum.
    (* Hsum is now Gt <> Gt, which is a contradiction *)
    elim Hsum.
    reflexivity.
Qed.