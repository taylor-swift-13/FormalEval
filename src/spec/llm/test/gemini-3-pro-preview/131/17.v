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

Example test_digits_spec_3 : digits_spec 3 3.
Proof.
  exists [3].
  split.
  - (* Prove: Forall (fun d => 0 <= d < 10) [3] *)
    constructor.
    + lia.
    + constructor.
  - split.
    + (* Prove: fold_left ... = 3 *)
      simpl. reflexivity.
    + split.
      * (* Prove: [3] <> [] -> hd 0 [3] <> 0 *)
        intros H. simpl. lia.
      * (* Prove parts related to 'odds' *)
        simpl. (* Reduces filter Z.odd [3] to [3] *)
        split.
        -- (* Prove: [3] = [] -> 3 = 0 *)
           intros H. discriminate H.
        -- (* Prove: [3] <> [] -> 3 = fold_right Z.mul 1 [3] *)
           intros H. simpl. reflexivity.
Qed.