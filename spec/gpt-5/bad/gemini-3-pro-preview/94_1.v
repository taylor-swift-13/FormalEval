Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

(* Specification Definitions *)

Definition int := Z.

Fixpoint sum_list (ds : list Z) : Z :=
  match ds with
  | nil => 0
  | d :: ds' => d + sum_list ds'
  end.

Fixpoint digits_value (ds : list Z) : Z :=
  match ds with
  | nil => 0
  | d :: ds' => d + 10 * digits_value ds'
  end.

Definition digit (d : Z) : Prop := 0 <= d <= 9.

Definition all_digits (ds : list Z) : Prop := Forall digit ds.

Definition divides_Z (d n : Z) : Prop := exists k : Z, n = d * k.

Definition prime_Z (n : Z) : Prop :=
  2 <= n /\ forall d : Z, 2 <= d < n -> ~ divides_Z d n.

Definition sum_digits_10 (n s : Z) : Prop :=
  0 <= n /\ exists ds : list Z, all_digits ds /\ digits_value ds = n /\ s = sum_list ds.

Definition max_prime_in_list (lst : list Z) (p : Z) : Prop :=
  In p lst /\ prime_Z p /\ forall y, In y lst -> prime_Z y -> y <= p.

Definition skjkasdkd_spec (lst : list int) (res : int) : Prop :=
  exists p : Z, max_prime_in_list lst p /\ sum_digits_10 p res.

(* Test Case Data *)

Definition test_input : list int := 
  [0; 3; 2; 1; 3; 5; 7; 4; 5; 5; 5; 2; 181; 32; 4; 32; 3; 2; 32; 324; 4; 3].

Definition test_output : int := 10.

(* Helper Lemmas *)

Lemma prime_181 : prime_Z 181.
Proof.
  split; [lia |].
  intros d Hd [k Hk].
  (* If d * k = 181, then d <= 13 or k <= 13 *)
  assert (H_bound: d <= 13 \/ k <= 13).
  {
    destruct (Z_le_gt_dec d 13); auto.
    destruct (Z_le_gt_dec k 13); auto.
    (* Both > 13 implies both >= 14 *)
    assert (d >= 14) by lia.
    assert (k >= 14) by lia.
    replace 181 with (d * k) in * by auto.
    assert (14 * 14 <= d * k). { apply Z.mul_le_mono_nonneg; lia. }
    lia.
  }
  
  destruct H_bound as [H_small_d | H_small_k].
  - (* Case d <= 13 *)
    assert (H_mod: 181 mod d = 0). { apply Z.mod_divide; [lia|]; exists k; auto. }
    (* Explicit check for d in 2..13 *)
    assert (H_cases : d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ d = 11 \/ d = 12 \/ d = 13 \/ d < 2 \/ d > 13) by lia.
    destruct H_cases as [?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|?]]]]]]]]]]]]]; subst; try (compute in H_mod; discriminate); try lia.
    
  - (* Case k <= 13 *)
    (* Establish k >= 2 *)
    assert (k >= 2).
    {
      destruct (Z_le_dec k 1); [|lia].
      assert (k <= 0 \/ k = 1) by lia. destruct H; [|subst k; lia].
      replace 181 with (d*k) in *; auto. assert (d*k <= 0) by (apply Z.mul_nonneg_nonpos; lia). lia.
    }
    assert (H_mod: 181 mod k = 0). 
    { apply Z.mod_divide; [lia|]; exists d; rewrite Z.mul_comm; auto. }
    (* Explicit check for k in 2..13 *)
    assert (H_cases : k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k < 2 \/ k > 13) by lia.
    destruct H_cases as [?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|?]]]]]]]]]]]]]; subst; try (compute in H_mod; discriminate); try lia.
Qed.

Lemma not_prime_324 : ~ prime_Z 324.
Proof.
  intros [_ H].
  specialize (H 2).
  assert (2 <= 2 < 324) by lia.
  apply H in H0.
  apply H0.
  exists 162. reflexivity.
Qed.

(* Main Proof *)

Theorem example_proof : skjkasdkd_spec test_input test_output.
Proof.
  unfold skjkasdkd_spec, test_input, test_output.
  exists 181.
  split.
  
  - (* max_prime_in_list *)
    split.
    + (* In 181 list *)
      simpl. repeat (left; reflexivity || right).
    + split.
      * (* prime_Z 181 *)
        apply prime_181.
      * (* forall y, In y list -> prime_Z y -> y <= 181 *)
        intros y Hy Hprime.
        simpl in Hy.
        (* Check every element in the list *)
        repeat (destruct Hy as [Heq | Hy]; [subst y; try lia | ]).
        (* Case y = 324, where lia fails *)
        { exfalso. apply not_prime_324. apply Hprime. }
        (* End of list *)
        { contradiction. }
        
  - (* sum_digits_10 181 10 *)
    split; [lia |].
    (* Digits of 181 (little-endian): [1; 8; 1] *)
    exists [1; 8; 1].
    split.
    + (* all_digits *)
      unfold all_digits, digit.
      repeat constructor; lia.
    + split.
      * (* digits_value *)
        simpl. lia.
      * (* sum_list *)
        simpl. lia.
Qed.