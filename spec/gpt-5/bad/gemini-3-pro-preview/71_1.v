Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_sqrt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.

Open Scope R_scope.

Definition triangle_area_spec (a b c area : R) : Prop :=
((a + b <= c \/ a + c <= b \/ b + c <= a) /\ area = -1) \/
(~(a + b <= c \/ a + c <= b \/ b + c <= a) /\
 let p := (a + b + c) / 2 in
 let x := sqrt (p * (p - a) * (p - b) * (p - c)) in
 exists k : Z,
   area = IZR k / 100 /\
   forall n : Z,
     Rabs (x * 100 - IZR k) <= Rabs (x * 100 - IZR n) /\
     (n <> k -> Rabs (x * 100 - IZR k) = Rabs (x * 100 - IZR n) -> Zeven k)).

Example triangle_3_4_5 : triangle_area_spec 3 4 5 6.
Proof.
  unfold triangle_area_spec.
  right.
  split.
  - (* Prove triangle inequality holds (negation of invalidity) *)
    intro H.
    destruct H as [H | [H | H]]; apply Rle_not_lt in H; apply H.
    + replace (3 + 4) with 7 by ring.
      apply IZR_lt. reflexivity.
    + replace (3 + 5) with 8 by ring.
      apply IZR_lt. reflexivity.
    + replace (4 + 5) with 9 by ring.
      apply IZR_lt. reflexivity.
  - (* Calculate p, x and prove rounding *)
    replace ((3 + 4 + 5) / 2) with 6 by (field; discrR).
    replace (6 * (6 - 3) * (6 - 4) * (6 - 5)) with 36 by ring.
    
    assert (Hsqrt: sqrt 36 = 6).
    {
      apply Rsqr_inj.
      - apply sqrt_pos.
      - apply IZR_le. apply Z.le_ge. apply Z.ge_le. vm_compute. intro; discriminate.
      - rewrite Rsqr_sqrt.
        + unfold Rsqr. ring.
        + apply IZR_le. apply Z.le_ge. apply Z.ge_le. vm_compute. intro; discriminate.
    }
    rewrite Hsqrt.
    
    (* Existential witness k = 600 *)
    exists 600%Z.
    split.
    + (* Prove area = 600/100 *)
      (* 6 = 600/100 *)
      field. discrR.
    + (* Prove rounding properties *)
      intros n.
      split.
      * (* Distance inequality *)
        replace (6 * 100 - IZR 600) with 0.
        2: { 
          replace (6 * 100) with (IZR 600).
          - ring.
          - rewrite <- mult_IZR. reflexivity.
        }
        rewrite Rabs_R0.
        apply Rabs_pos.
      * (* Tie-breaking condition *)
        intros Hneq Heq.
        replace (6 * 100 - IZR 600) with 0 in Heq.
        2: { 
          replace (6 * 100) with (IZR 600).
          - ring.
          - rewrite <- mult_IZR. reflexivity.
        }
        rewrite Rabs_R0 in Heq.
        symmetry in Heq.
        apply Rabs_eq_0 in Heq.
        (* Heq is 0 = 6*100 - IZR n *)
        assert (Hn: IZR 600 = IZR n).
        {
          rewrite <- Heq.
          replace (6 * 100) with (IZR 600).
          - reflexivity.
          - rewrite <- mult_IZR. reflexivity.
        }
        apply eq_IZR in Hn.
        contradiction Hneq. rewrite Hn. reflexivity.
Qed.