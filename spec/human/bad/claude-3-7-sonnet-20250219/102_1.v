Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition problem_102_pre (x y : Z) : Prop := x > 0 /\ y > 0.

Definition problem_102_spec (x y res : Z) : Prop :=
  ( (exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    (Z.even res = true /\ x <= res /\ res <= y /\
     forall z' : Z, res < z' /\ z' <= y -> Z.even z' = false) )
  /\
  ( (~ exists z : Z, x <= z /\ z <= y /\ Z.even z = true) -> res = -1 ).

(* Definition of choose_num: largest even number in [x,y], or -1 if none *)
Definition choose_num (x y : Z) : Z :=
  if Z.leb y x then -1
  else
    let cand := if Z.even y then y else y - 1 in
    if Z.ltb cand x then -1 else cand.

Example test_choose_num_12_15 :
  problem_102_spec 12 15 (choose_num 12 15).
Proof.
  unfold problem_102_spec, choose_num.
  split.
  - intros Hex.
    destruct Hex as [z [Hzx [Hzy Hevenz]]].
    (* cand = if even 15 then 15 else 14 *)
    assert (Heven_15 : Z.even 15 = false).
    { reflexivity. }
    rewrite Heven_15.
    set (cand := 15 - 1).
    assert (cand = 14) by lia.
    rewrite H.
    destruct (Z.ltb_spec 14 12).
    { lia. }
    split.
    + (* Z.even res = true *)
      unfold Z.even.
      rewrite Z.even_spec.
      rewrite Z.rem_mod.
      simpl.
      reflexivity.
    + split.
      * lia.
      * split.
        -- lia.
        -- intros z' [Hz'gt Hz'le].
           (* Candidate is 14, show no even z' >14 and <=15 *)
           destruct (Z.eq_dec z' 15) as [Hz'eq|Hz'neq].
           ++ subst z'.
              rewrite Z.even_spec.
              unfold Z.even.
              rewrite Z.rem_mod.
              simpl.
              (* 15 mod 2 = 1 → odd *)
              reflexivity.
           ++ assert (z' < 15) by lia.
              lia.
  - intros Hnoeven.
    (* show res = -1 *)
    destruct (Z.leb_spec 15 12).
    + reflexivity.
    + simpl.
      destruct (Z.even 15) eqn:Heven15.
      * destruct (Z.ltb_spec 15 12).
        -- reflexivity.
        -- exfalso.
           apply Hnoeven.
           exists 15.
           lia.
           split; try lia.
           rewrite Heven15.
           reflexivity.
      * (* cand = 14 *)
        destruct (Z.ltb_spec 14 12).
        -- reflexivity.
        -- exfalso.
           apply Hnoeven.
           exists 14.
           lia.
           split; try lia.
           unfold Z.even in Heven15.
           rewrite Z.even_spec in Heven15.
           rewrite Z.even_spec.
           (* Since 15 mod 2=1, 14 mod 2=0 *)
           replace (Z.rem 14 2) with 0.
           ++ reflexivity.
           ++ rewrite Z.rem_mod.
              simpl.
              reflexivity.
Qed.