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

Example test_digits_spec_997 : digits_spec 997 567.
Proof.
  exists [9; 9; 7].
  split.
  - (* Prove: Forall (fun d => 0 <= d < 10) [9; 9; 7] *)
    repeat constructor; lia.
  - split.
    + (* Prove: fold_left ... = 997 *)
      simpl. reflexivity.
    + split.
      * (* Prove: [9; 9; 7] <> [] -> hd 0 [9; 9; 7] <> 0 *)
        intros H. simpl. lia.
      * (* Prove parts related to 'odds' *)
        simpl. (* Reduces filter Z.odd [9; 9; 7] to [9; 9; 7] *)
        split.
        -- (* Prove: [9; 9; 7] = [] -> 567 = 0 *)
           intros H. discriminate H.
        -- (* Prove: [9; 9; 7] <> [] -> 567 = fold_right Z.mul 1 [9; 9; 7] *)
           intros H. simpl. reflexivity.
Qed.