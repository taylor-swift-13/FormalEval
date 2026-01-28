Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.

Open Scope string_scope.

Definition get_char (s : string) (n : nat) : ascii :=
  match String.get n s with
  | Some c => c
  | None => " "%char
  end.

(* Pre: no additional constraints for `encode/decode_cyclic` by default *)
Definition problem_38_pre (input : string) : Prop := True.

Definition problem_38_spec (input output : string) : Prop :=
  (* 1. Basic constraint: lengths must be equal *)
  String.length input = String.length output /\
  (
    (* 2. Define constants *)
    let n := ((String.length input / 3) * 3 - 1)%nat in
    let L := String.length input in

    (* 3. For all indices i, assertions must hold *)
    forall i, (i < L)%nat ->
      let out_char := get_char output i in
      (
        (* Case 1: i <= n *)
        ( (i <= n)%nat ->
          (
            (* Subcase 1: (i+1)%3 = 1 *)
            ( ((i + 1) mod 3 = 1%nat) /\ (out_char = get_char input (i + 2)) ) \/

            (* Subcase 2: (i+1)%3 = 2 or 0 *)
            ( (((i + 1) mod 3 = 2%nat) \/ ((i + 1) mod 3 = 0%nat)) /\ (out_char = get_char input (i - 1)) )
          )
        ) /\

        (* Case 2: i > n *)
        ( (~(i <= n)%nat) ->
          (
            out_char = get_char input i
          )
        )
      )
  ).

(* Helper functions and lemmas for checking the property on concrete strings *)

Fixpoint forallb_range (n : nat) (f : nat -> bool) : bool :=
  match n with
  | 0 => true
  | S n' => f n' && forallb_range n' f
  end.

Lemma forallb_range_spec : forall n f,
  forallb_range n f = true -> forall i, i < n -> f i = true.
Proof.
  induction n; intros f H i Hi.
  - lia.
  - simpl in H. apply andb_true_iff in H. destruct H as [Hf Hrec].
    destruct (Nat.eq_dec i n).
    + subst. assumption.
    + apply IHn; try assumption. lia.
Qed.

Definition check_problem_38 (input output : string) : bool :=
  let len_in := String.length input in
  let len_out := String.length output in
  (len_in =? len_out) &&
  (
    let n := ((len_in / 3) * 3 - 1)%nat in
    let check_i (i : nat) : bool :=
      let out_char := get_char output i in
      let in_char_at (k : nat) := get_char input k in
      let mod3 := (i + 1) mod 3 in
      if (i <=? n) then
        if (mod3 =? 1) then
          Ascii.eqb out_char (in_char_at (i + 2))
        else if (mod3 =? 2) || (mod3 =? 0) then
          Ascii.eqb out_char (in_char_at (i - 1))
        else false
      else
        Ascii.eqb out_char (in_char_at i)
    in
    forallb_range len_in check_i
  ).

Lemma check_problem_38_correct : forall input output,
  check_problem_38 input output = true -> problem_38_spec input output.
Proof.
  intros input output H.
  unfold check_problem_38 in H.
  apply andb_true_iff in H. destruct H as [Hlen Hforall].
  apply Nat.eqb_eq in Hlen.
  unfold problem_38_spec.
  split.
  - assumption.
  - intros i Hi.
    pose proof (forallb_range_spec (String.length input) _ Hforall i Hi) as Hcheck.
    cbn in Hcheck.
    destruct (i <=? (String.length input / 3) * 3 - 1) eqn:Hle.
    + (* i <= n *)
      apply Nat.leb_le in Hle.
      split.
      * intros _.
        destruct ((i + 1) mod 3) eqn:Hmod.
        { (* mod = 0 *)
          right. split; [ right; reflexivity | ].
          rewrite Hmod in Hcheck.
          simpl in Hcheck. rewrite orb_true_r in Hcheck.
          apply Ascii.eqb_eq in Hcheck. assumption.
        }
        { (* mod = 1 or > 1 *)
          destruct n0.
          - (* 1 *)
            left. split; [ reflexivity | ].
            rewrite Hmod in Hcheck.
            simpl in Hcheck. apply Ascii.eqb_eq in Hcheck. assumption.
          - (* > 1 *)
             destruct n0.
             + (* 2 *)
               right. split; [ left; reflexivity | ].
               rewrite Hmod in Hcheck.
               simpl in Hcheck. rewrite orb_false_r in Hcheck.
               apply Ascii.eqb_eq in Hcheck. assumption.
             + (* > 2, impossible for mod 3 *)
               exfalso.
               assert (Hlt: (i + 1) mod 3 < 3) by apply Nat.mod_upper_bound; lia.
               rewrite Hmod in Hlt. lia.
        }
      * (* i > n branch vacuous *)
        intros Hcontra. exfalso. apply Hcontra. assumption.
    + (* i > n *)
      apply Nat.leb_nle in Hle.
      split.
      * intros Hcontra. exfalso. apply Hle. assumption.
      * intros _.
        apply Ascii.eqb_eq in Hcheck. assumption.
Qed.

Example test_problem_38 : problem_38_spec 
  "Testing567The quick Testing567The quick brown fox jumps over the lazy dog.0 123abcdefghijklmnopqrstuvwxyz,Testing 123, testing 123. testingabc 123.brown fox jumps over the lazy dog.0 123,Testing 123, testing 123. testingabc 123."
  "sTenti6g5h7Tqe cuiTk tesgin756eThu qkicr bnowo fjx pumos rveh tle yazo d0g.2 1b3aecdhfgkijnlmqoptrswuvzxye,Tist ng312t, tesgin2 1 3.stentibga1c .23obr wnxfou jsmpv o eretha l zygdo .0312e,Tist ng312t, tesgin2 1 3.stentibga1c .23".
Proof.
  apply check_problem_38_correct.
  vm_compute.
  reflexivity.
Qed.