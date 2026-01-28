Require Import Arith.
Require Import Lia.

(* Pre: require `input >= 2` so that a largest proper divisor exists *)
Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  (* 1. output 是 input 的一个因数 *)
  input mod output = 0 /\

  (* 2. output 严格小于 input *)
  output < input /\

  (* 3. 对于任何严格小于 input 的正因数 i, i 都小于等于 output *)
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example problem_24_test : problem_24_spec 29 1.
Proof.
  unfold problem_24_spec.
  split.
  - simpl. reflexivity.
  - split.
    + lia.
    + intros i [Hi_pos Hi_lt] Hi_div.
      assert (i = 1 \/ (2 <= i /\ i <= 28)) as Hi_cases by lia.
      destruct Hi_cases as [Hi_eq1 | Hi_range].
      * lia.
      * destruct (Nat.eq_dec i 2) as [H2|H2]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 3) as [H3|H3]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 4) as [H4|H4]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 5) as [H5|H5]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 6) as [H6|H6]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 7) as [H7|H7]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 8) as [H8|H8]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 9) as [H9|H9]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 10) as [H10|H10]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 11) as [H11|H11]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 12) as [H12|H12]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 13) as [H13|H13]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 14) as [H14|H14]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 15) as [H15|H15]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 16) as [H16|H16]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 17) as [H17|H17]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 18) as [H18|H18]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 19) as [H19|H19]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 20) as [H20|H20]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 21) as [H21|H21]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 22) as [H22|H22]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 23) as [H23|H23]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 24) as [H24|H24]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 25) as [H25|H25]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 26) as [H26|H26]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 27) as [H27|H27]. { subst. simpl in Hi_div. discriminate. }
        destruct (Nat.eq_dec i 28) as [H28|H28]. { subst. simpl in Hi_div. discriminate. }
        lia.
Qed.