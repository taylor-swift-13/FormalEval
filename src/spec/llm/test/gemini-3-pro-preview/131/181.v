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

Example test_digits_spec_72 : digits_spec 72 7.
Proof.
  exists [7; 2].
  split.
  - (* Prove: Forall (fun d => 0 <= d < 10) [7; 2] *)
    constructor.
    + lia.
    + constructor.
      * lia.
      * constructor.
  - split.
    + (* Prove: fold_left ... = 72 *)
      simpl. reflexivity.
    + split.
      * (* Prove: [7; 2] <> [] -> hd 0 [7; 2] <> 0 *)
        intros H. simpl. lia.
      * (* Prove parts related to 'odds' *)
        simpl. (* Reduces filter Z.odd [7; 2] to [7] *)
        split.
        -- (* Prove: [7] = [] -> 7 = 0 *)
           intros H. discriminate H.
        -- (* Prove: [7] <> [] -> 7 = fold_right Z.mul 1 [7] *)
           intros H. simpl. reflexivity.
Qed.