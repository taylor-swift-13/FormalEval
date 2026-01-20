Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition digits_spec (n : Z) (res : Z) : Prop :=
  exists l : list Z,
    Forall (fun d => 0 <= d < 10) l /\
    fold_left (fun acc d => 10 * acc + d) l 0 = n /\
    (l <> [] -> hd 0 l <> 0) /\
    let odds := filter Z.odd l in
    (odds = [] -> res = 0) /\
    (odds <> [] -> res = fold_right Z.mul 1 odds).

Example test_digits_spec_123456786 : digits_spec 123456786 105.
Proof.
  exists [1; 2; 3; 4; 5; 6; 7; 8; 6].
  split.
  - repeat constructor; lia.
  - split.
    + simpl. reflexivity.
    + split.
      * intros H. simpl. lia.
      * simpl. split.
        -- intros H. discriminate H.
        -- intros H. reflexivity.
Qed.